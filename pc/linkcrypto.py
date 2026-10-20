# LIFESPAN: permanent
"""The fast link's authentication and encryption (protocol v2), shared by the PC receiver and its tests. The Java twin is src/io/github/exalt24/phonekb/LinkCrypto.java; both are checked against the same test vectors.

The pairing code is 16 random characters (about 79 bits) and never crosses the wire. Per connection the PC and the phone swap fresh nonces and each proves it knows the code:
    PC    -> phone: 0x7E | nc(16)
    phone -> PC:    ns(16) | HMAC(K, "phone" | nc | ns)          the PC checks this BEFORE it trusts anything the phone sends
    PC    -> phone: HMAC(K, "pc" | ns | nc)
    phone -> PC:    'K'
Then every 8-byte frame is sent as 16 bytes: the frame XOR a keystream block, plus a truncated HMAC over a per-direction counter (so a frame cannot be forged, replayed or reordered; a bad tag ends the connection).
"""
import hashlib
import hmac
import os
import re
import struct

ALPHABET = "abcdefghjkmnpqrstuvwxyz23456789"
CODE_LEN = 16


def normalize(text):
    """The code as typed (spaces and hyphens allowed, any case) -> its canonical 16 characters, or None when it is not a valid code."""
    t = re.sub(r"[\s-]", "", text or "").lower()
    return t if len(t) == CODE_LEN and all(c in ALPHABET for c in t) else None


def pretty(code):
    return "-".join(code[i:i + 4] for i in range(0, CODE_LEN, 4))


def derive_key(code):
    return hashlib.sha256(("phonekb-v2|" + code).encode("ascii")).digest()


def mac(key, *parts):
    return hmac.new(key, b"".join(parts), hashlib.sha256).digest()


def proof_phone(key, nc, ns):
    return mac(key, b"phone", nc, ns)


def proof_pc(key, nc, ns):
    return mac(key, b"pc", ns, nc)


class Session:
    """One connection's frame sealing. phone_side False on the PC: it sends direction 1 and receives direction 0."""

    def __init__(self, key, nc, ns, phone_side):
        self.key = key          # which pairing code made this link: the receiver ends a link whose key is no longer the one on disk
        self.kenc = mac(key, b"enc", nc, ns)
        self.kmac = mac(key, b"mac", nc, ns)
        self.send_dir = 0 if phone_side else 1
        self.recv_dir = 1 - self.send_dir
        self.send_seq = 0
        self.recv_seq = 0

    def seal(self, frame):
        assert len(frame) == 8
        seq = struct.pack(">Q", self.send_seq)
        self.send_seq += 1
        d = bytes([self.send_dir])
        ks = mac(self.kenc, d, seq)[:8]
        ct = bytes(a ^ b for a, b in zip(frame, ks))
        return ct + mac(self.kmac, d, seq, ct)[:8]

    def open(self, wire):
        """The 8-byte frame, or None when the length or the tag is wrong (the caller must close the connection)."""
        if len(wire) != 16:
            return None
        seq = struct.pack(">Q", self.recv_seq)
        d = bytes([self.recv_dir])
        ct, tag = wire[:8], wire[8:]
        if not hmac.compare_digest(tag, mac(self.kmac, d, seq, ct)[:8]):
            return None
        self.recv_seq += 1
        ks = mac(self.kenc, d, seq)[:8]
        return bytes(a ^ b for a, b in zip(ct, ks))


# ---- pairing by two short typed numbers (like a Bluetooth passkey), so nobody has to type 16 characters --------------------------------------------------------------------------------
# The phone and the PC run a Diffie-Hellman exchange (RFC 3526 group 14, 2048 bits). The PC commits to its public value first (so a man in the middle cannot pick one that makes the numbers match),
# both derive two 6 digit numbers from the shared secret and the whole transcript: the PC shows the first (pair_sas) and the person TYPES it on the phone, which shows none; only a right entry makes the
# phone show the second (pair_check), which the person types in the PC window. A listener that merely follows the protocol knows both numbers but has no screen in front of the person, so it cannot be
# paired by a reflex tap in either direction. The phone sends 'Y' as soon as its person typed the first number right; the PC sends 'Y' once the second was typed right; the phone then stores the code and
# sends one 'K', and only then does the PC store it. Both sides derive the same 16 character code from the secret and the ordinary link (above) takes over: pairing adds no new way to connect.
#     PC -> phone: 0x7D | commit(32)             commit = SHA256("phonekb-pair-commit" | pubC | nc)
#     phone -> PC: pubS(256) | ns(16)
#     PC -> phone: pubC(256) | nc(16)            the phone checks it against the commit
#     each way:    'Y' or 'N' | HMAC(kz, "confirm-phone"/"confirm-pc" | transcript)      the phone's once its person typed the first number, the PC's once its person typed the second
#     phone -> PC: 'K'                           the phone has stored the code
DH_P = int(
    "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F40"
    "6B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E46"
    "2E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF", 16)
DH_G = 2
PUB_LEN = 256
PAIR_HELLO = 0x7D


def dh_keypair(rand32=None):
    """(private, public): a 256 bit exponent is plenty for this group and keeps the phone fast."""
    priv = int.from_bytes(rand32 or os.urandom(32), "big") | (1 << 255)
    return priv, pow(DH_G, priv, DH_P)


def pub_bytes(pub):
    return pub.to_bytes(PUB_LEN, "big")


def valid_pub(pub):
    """A peer's public value must not be 0, 1 or p-1 (the only tiny-order values of a safe prime group)."""
    return 2 <= pub <= DH_P - 2


def pair_commit(pub_c_bytes, nc):
    return hashlib.sha256(b"phonekb-pair-commit" + pub_c_bytes + nc).digest()


def pair_secret(priv, other_pub):
    return hashlib.sha256(pow(other_pub, priv, DH_P).to_bytes(PUB_LEN, "big")).digest()


def pair_transcript(pub_c_bytes, nc, pub_s_bytes, ns):
    return pub_c_bytes + nc + pub_s_bytes + ns


def pair_sas(kz, transcript):
    """The first 6 digit number: the PC shows it and the person types it on the phone."""
    return "%06d" % (int.from_bytes(mac(kz, b"sas", transcript)[:4], "big") % 1000000)


def pair_check(kz, transcript):
    """The second 6 digit number: the phone shows it only AFTER the person typed the first one on it correctly, and the person types it on the PC. A device that is not a real phone with a screen in front of the person cannot show it to anyone, so it cannot get past the PC."""
    return "%06d" % (int.from_bytes(mac(kz, b"check", transcript)[:4], "big") % 1000000)


def pair_confirm(kz, who, transcript):
    """who is b'phone' or b'pc': proves the sender computed the same secret and said yes."""
    return mac(kz, b"confirm-" + who, transcript)


def pair_code(kz, transcript):
    """The 16 character code both sides store once the person has confirmed."""
    d = mac(kz, b"code", transcript)
    return "".join(ALPHABET[b % len(ALPHABET)] for b in d[:CODE_LEN])
