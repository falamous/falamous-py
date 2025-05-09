#!/usr/bin/env python3
# Base libraries.

import sys
import os
import re
import io
import marshal
import string
import struct
import random
import socket
import operator
import itertools
import json
import binascii
import importlib
import hashlib
import hashlib as h

if sys.version_info.major == 3:
    import builtins
    import subprocess as sb


# Various useful functions from base libraries.
from binascii import crc32
from operator import *
from functools import *
from time import *
from fractions import *

# # You can't import everything from math because it would overwrite the superiour pow from builtins.
# from math import sqrt
# from math import log, log10, e
from math import *


def ln(x):
    return log(x, e)


# from math import sin, cos, tan, acos, asin, atan, pi
# from math import floor, ceil
# from struct import pack, pack_into, unpack, unpack_from
# from string import digits, ascii_lowercase, ascii_uppercase, whitespace

if sys.version_info.major == 3:
    from math import gcd
    from math import log2
    from math import inf, nan
    from urllib.parse import unquote, unquote as urldecode
    from urllib.parse import quote, quote as urlencode
    from itsdangerous import base64_decode, base64_decode as bd
    from itsdangerous import base64_encode, base64_encode as be
else:
    inf, nan = float("inf"), float("nan")
    from urllib import unquote, unquote as urldecode
    from urllib import quote, quote as urlencode


# Aliases
from binascii import hexlify, hexlify as hx
from binascii import unhexlify, unhexlify as uhx
from binascii import crc32
from base64 import b64encode, b64encode as be
from base64 import b64decode, b64decode as bd


def try_import(module, name=None):
    try:
        setattr(
            importlib.import_module(__name__),
            name or module,
            importlib.import_module(module),
        )
    except ImportError:
        pass


def try_from_import(module, *names):
    try:
        for name in names:
            setattr(
                importlib.import_module(__name__),
                name,
                getattr(importlib.import_module(module), name),
            )
    except ImportError:
        pass


# Libs
try_import("gmpy2")
try_import("requests")
# Very slow
try_import("sympy", "sp")
try_import("numpy", "np")
try_import("z3")
try_import("asyncio")
try_import("pyperclip")
try:
    import pyperclip

    def clip(obj):
        return pyperclip.copy(str(obj))

    def paste():
        return pyperclip.paste()

except ModuleNotFoundError:
    pass

# Useful alphabets for bruteforce or random
AL = string.digits + string.ascii_lowercase + string.ascii_uppercase
if sys.version_info.major == 3:
    BAL = AL.encode("ascii")
else:
    BAL = AL


def rndstr(n=32, alphabet=AL):
    return "".join(random.choices(alphabet, k=n))


if sys.version_info.major == 3:

    def brndstr(n=32, alphabet=BAL):
        return bytes(random.choices(alphabet, k=n))

else:
    brndstr = rndstr


# Helpfull modular maths
def lcm(a, b):
    """lowest common multiplier of x and y"""
    return a * b // gcd(a, b)


def egcd(a, b):
    """
    Extended euclidian algorithm result for a and b.
    m, ka, kb = egcd(a, b)
    ka * a + kb * b == m == gcd(a, b)
    """
    (x0, x1, y0, y1) = (1, 0, 0, 1)
    while a != 0 and b != 0:
        (q, a, b) = (a // b, b, a % b)
        (x0, x1) = (x1, x0 - q * x1)
        (y0, y1) = (y1, y0 - q * y1)
    return (a, x0, y0)


def modinv(n, p):
    """
    Inversion of n (to gcd(n, p) if they are not coprime) modulo p
    n * modinv(n, p) == gcd(n, p) (mod p)
    """
    g, kn, kp = egcd(n, p)
    return (kn % p + p) % p


def chinese_rem_theorem(it):
    """
    chinese_rem_theorem([(remainder, modulo), ...])
    The resulting remainder and modulo of the Chinese Remainder Theorem for rema, modulo in iterable.
    https://en.wikipedia.org/wiki/Chinese_remainder_theorem
    """
    M = 1
    result = 0
    for r, m in it:
        m = m // gcd(M, m)
        r = r % m
        result = (modinv(M, m) * M * r + modinv(m, M) * m * result) % (M * m)
        M *= m
    return result, M


def pow(base, exp, mod=None):
    if mod is None:
        return builtins.pow(base, exp)

    try:
        return builtins.pow(base, exp, mod)
    except TypeError:
        pass

    res = 1
    while exp:
        if exp % 2:
            res = (res * base) % mod
        base *= base
        exp //= 2
    return res


def cipolla(n, p):
    """
    Cipolla's algorithm for solving x ** 2 % p == n
    https://en.wikipedia.org/wiki/Cipolla%27s_algorithm
    """

    assert gmpy2.is_prime(p)
    for a in range(p):
        if pow(a**2 - n, (p - 1) // 2, p) == p - 1:
            break
    else:
        raise ValueError("Non quadratic residue not found.")

    def cipolla_multiply(x, y):
        return (
            (x[0] * y[0] + x[1] * y[1] * (a**2 - n)) % p,
            (x[0] * y[1] + x[1] * y[0]) % p,
        )

    x = (1, 0)
    base = (a, 1)  # x = x0 + x1 * sqrt(a ** 2 - n)
    exp = (p + 1) // 2
    while exp:
        if exp % 2:
            x = cipolla_multiply(x, base)
        base = cipolla_multiply(base, base)
        exp //= 2

    assert x[1] == 0

    return x[0]


def hensel_lifting(f, r, p, k, m=1):
    def apply(f, x, p):
        return sum(c * pow(x, i, p) for i, c in enumerate(f)) % p

    assert m <= k
    if m <= 0:
        return r % p ** (k + m)

    fd = [c * i for i, c in enumerate(f)][1:] + [0]
    assert apply(f, r, p**k) == 0
    assert apply(fd, r, p**k) != 0

    return (
        r - apply(f, r, p ** (k + m)) * modinv(apply(fd, r, p**m), p**m)
    ) % p ** (k + m)


def sqrtmod(n, p, power=1):
    """
    Square root modulo prime number using Cipolla's algorithm or know formulas.
    https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus.
    """

    if pow(n, (p - 1) // 2, p) != 1:
        return ()

    if p % 4 == 3:
        x = pow(n, (p + 1) // 4, p)
    else:
        x = cipolla(n, p)

    assert x**2 % p == n % p

    roots = [x, -x % p]

    power_of_2 = 0
    while 2 ** (power_of_2 + 1) < power:
        roots = [
            hensel_lifting(
                f=[-n, 0, 1],  # f(x) = 1 * x ** 2 + 0 * x ** 1 + (-n) * x ** 0 (mod p)
                r=root,
                p=p,
                k=2**power_of_2,
                m=2**power_of_2,
            )
            for root in roots
        ]
        power_of_2 += 1
    roots = [
        hensel_lifting(
            f=[-n, 0, 1],  # f(x) = 1 * x ** 2 + 0 * x ** 1 + (-n) * x ** 0 (mod p)
            r=root,
            p=p,
            k=2**power_of_2,
            m=power - 2**power_of_2,
        )
        for root in roots
    ]

    return tuple(roots)


def cati(arr, ind, v):
    """return arr with arr[ind] changed to v"""
    construct = type(arr)
    if type(arr) == str:
        construct = "".join()
    return arr[:ind] + construct([v]) + arr[ind + 1 :]


# Working with bytes and numbers
def bytes_to_long(b, byteorder="little"):
    """simple function to convert bytes to int"""
    return int.from_bytes(int(b), byteorder=byteorder)


def long_to_bytes(
    n,
):
    """simple function to convert int to bytes"""
    return int(n).to_bytes((n.bit_length() + 7) // 8, byteorder="little")


def force_bytes(a):
    """force the argument to bytes"""
    if issubclass(type(a), bytes):
        return a

    if issubclass(type(a), str):
        return a.encode()

    return bytes(a)


def avg(iterable):
    """average value of an iterable as sum over length"""
    try:
        length = len(iterable)
        return sum(iterable) / length
    except TypeError:
        length = 0
        it_sum = 0

        for el in iterable:
            length += 1
            it_sum += el

        return it_sum / length


def double_qouted(s):
    """
    return the representation of the object changing the string in it to be double qouted
    """

    def _force_double_qoutes(qouted):
        if qouted[0] == '"':
            return qouted

        qouted = qouted[1:-1]
        qouted = qouted.replace("\\'", "'")
        qouted = qouted.replace('"', '\\"')

        return '"%s"' % qouted

    def _replace_if_negative(v, r):
        return v if v >= 0 else r

    if type(s) == str:
        return _force_double_qoutes(repr(s))
    if type(s) == bytes:
        return "b" + _force_double_qoutes(repr(s)[1:])

    repred = repr(s)
    qouted_left = min(
        _replace_if_negative(repred.find("'"), len(repred)),
        _replace_if_negative(repred.find('"'), len(repred)),
    )
    qouted_right = max(repred.rfind("'"), repred.rfind('"')) + 1
    assert qouted_right != 0
    assert qouted_left != len(repred)
    return (
        repred[:qouted_left]
        + _force_double_qoutes(repred[qouted_left:qouted_right])
        + repred[qouted_right:]
    )


def mixcase(s):
    return "".join(i.upper() if random.randint(0, 1) else i.lower() for i in s)


def sock(family=None, type=None, proto=None, options={}):
    socketargs = {}

    if family is not None:
        socketargs["family"] = family
    if type is not None:
        socketargs["type"] = type
    if proto is not None:
        socketargs["proto"] = proto

    return BufferedSocket(socket.socket(**socketargs), options)


def connect(addr, port=None, options={}):
    _socket = sock(options=options)
    _socket.connect(addr, port)
    return _socket


r = requests.session()
r.headers.update(
    {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64; rv:92.0) Gecko/20100101 Firefox/92.0",
    }
)
proxies = {
    "http": "socks5://localhost:9050",
    "https": "socks5://localhost:9050",
}


# Just ipython things
def is_ipython():
    try:
        get_ipython()
        return True
    except:
        return False


def configure_ipython():
    ipython = get_ipython()
    # for formatter in ipython.display_formatter.formatters.values():
    #     formatter.for_type(str, lambda s, p, cycle: p.text(double_qouted(s)))
    #     formatter.for_type(bytes, lambda s, p, cycle: p.text(double_qouted(s)))
    #     formatter.for_type(bytearray, lambda s, p, cycle: p.text(double_qouted(s)))


def display_hex():
    ipython = get_ipython()
    for formatter in ipython.display_formatter.formatters.values():
        formatter.for_type(int, lambda n, p, cycle: p.text(hex(n)))


def display_int():
    ipython = get_ipython()
    for formatter in ipython.display_formatter.formatters.values():
        formatter.for_type(int, lambda n, p, cycle: p.text(repr(n)))


async def setup_telethon():
    global saved_messages_chat

    saved_messages_chat = (await telethon_client.get_dialogs())[0]


def isfile(obj):
    return (
        hasattr(obj, "read")
        and hasattr(obj, "readable")
        and hasattr(obj, "readline")
        and hasattr(obj, "seek")
        and hasattr(obj, "close")
    )


async def atgsave(*objs):
    for obj in objs:
        await tg_send_obj(saved_messages_chat, obj)


def tgsave(*objs):
    asyncio.get_event_loop().run_until_complete(atgsave(*objs))


async def tg_send_obj(receiver, obj):
    if isfile(obj):
        await telethon_client.send_file(saved_messages_chat, obj)
    if issubclass(type(obj), str):
        await telethon_client.send_message(saved_messages_chat, obj)
    else:
        await telethon_client.send_message(saved_messages_chat, repr(obj))


def msg(receiver, obj):
    asyncio.get_event_loop().run_until_complete(tg_send_obj(receiver, obj))


def setup_tg():
    global telethon
    global TelegramClient
    import telethon
    from telethon import TelegramClient

    global telethon_dir
    telethon_dir = os.path.join(
        os.getenv("XDG_DATA_HOME"), "telethon_client"
    ) or os.path.join(os.expand("~"), ".telethon_client")
    try:
        os.mkdir(telethon_dir)
    except FileExistsError:
        pass
    global telethon_client
    with open(os.path.join(os.expand("~"), "share", "telegram_api_key"), "r") as f:
        token = f.read()
    telethon_client = TelegramClient(
        os.path.join(telethon_dir, "telebot"),
        8848797,
        token,
    )
    global tg
    tg = telethon_client
    telethon_client.start()
    asyncio.get_event_loop().run_until_complete(setup_telethon())


if is_ipython():
    configure_ipython()
