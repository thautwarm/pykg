from __future__ import annotations
from typing import Type
from collections import deque
from http.client import HTTPResponse
import socket
import types
import io
import time
import ssl
import typing

if typing.TYPE_CHECKING:
    from typing import TypeVar, Generator
    _T = TypeVar('_T')


# https://stackoverflow.com/questions/24728088/python-parse-http-response-string
class FakeSocket():
    def __init__(self, response_bytes):
        self._file = io.BytesIO(response_bytes)
    def makefile(self, *args, **kwargs):
        return self._file

Pending = None

def parse_http_response(response_bytes: bytes | bytearray):
    source = FakeSocket(response_bytes)
    response = HTTPResponse(source)  # type: ignore
    response.begin()
    return response

def async_apply(fn, arg, hang_on: Type[OSError] = BlockingIOError):
    while True:
        try:
            v = fn(arg)
            return v
        except hang_on as e:
            yield Pending


def async_socket_sendall(self: socket.socket, data):
    count = 0
    send = types.MethodType(socket.socket.send, self)
    with memoryview(data) as view, view.cast("B") as byte_view:
        amount = len(byte_view)
        while count < amount:
            v = yield from async_apply(send, byte_view[count:])
            count += v


def req_html(host, path):
    return b"GET /" + path + b" HTTP/1.0\r\nHost: " + host + b"\r\n\r\n"


def async_hand_shake(ssl_sock):
    count = 0
    while True:
        try:
            count += 1
            ssl_sock.do_handshake()
            break
        except ssl.SSLError:
            pass


def asleep(d: float):
    start = time.time()
    while time.time() - start < d:
        yield Pending


def aread_sock(ssl_sock, size, timeout: float = 60):
    start_time = time.time()
    while True:
        if time.time() - start_time > timeout:
            raise TimeoutError
        try:
            data = ssl_sock.recv(size)
            return data
        except ssl.SSLError:
            yield Pending
        except BlockingIOError:
            yield Pending
        except socket.timeout:
            yield Pending
        except socket.error:
            raise

def areadpage(url, timeout=10):
    protocol, _, host, path = url.split("/", 3)
    host, path = map(str.encode, (host, path))
    context = ssl.create_default_context()
    context = ssl.SSLContext(ssl.PROTOCOL_TLS)
    context.verify_mode = ssl.CERT_NONE
    context.check_hostname = False
    if protocol == "https:":
        port = 443
    elif protocol == "http:":
        port = 80
    else:
        raise IOError(f"unknown protocol: {protocol}")
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock, context.wrap_socket(
        sock, server_hostname=host
    ) as ssl_sock:
        ssl_sock.connect((host, port))
        start_time = time.time()
        request = req_html(host, path)
        # print(request.decode())
        ssl_sock.sendall(request)
        ssl_sock.setblocking(False)
        chunk = bytearray()
        while True:
            c = yield from aread_sock(ssl_sock, 1, timeout - (time.time() - start_time))
            chunk.extend(c)
            if chunk.endswith(b'\r\n\r\n'):
                break

        resp = parse_http_response(chunk)
        if resp.status != 200:
            return resp, b''

        ios = io.BytesIO()
        while True:
            data = yield from aread_sock(ssl_sock, 1024, timeout - (time.time() - start_time))
            if not data:
                return resp, ios.getvalue()
            ios.write(data)


def get_async_result(gen):
    try:
        while True:
            next(gen)

    except StopIteration as e:
        return e.value


def gather(gens: list):
    results = []
    tasks = deque()
    for i in range(len(gens)):
        results.append(None)
        tasks.append((i, gens[i]))
    while tasks:
        i, gen = tasks.popleft()
        try:
            next(gen)
            yield
        except StopIteration as e:
            results[i] = e.value
            continue
        tasks.append((i, gen))
    return results


def gather_with_limited_workers(gens: list, nworkers: int = 16):
    results = []
    alltasks = deque()
    for i in range(len(gens)):
        results.append(None)
        alltasks.append((i, gens[i]))
    tasks = deque()
    while nworkers and alltasks:
        tasks.append(alltasks.popleft())
        nworkers -= 1
    while alltasks or tasks:
        i, gen = tasks.popleft()
        try:
            next(gen)
            yield
        except StopIteration as e:
            results[i] = e.value
            if alltasks:
                tasks.append(alltasks.popleft())
            continue
        tasks.append((i, gen))

    return results


def run_many(gens: list[Generator[None, None, _T]]) -> list[_T]:
    results = []
    tasks = deque()
    for i in range(len(gens)):
        results.append(None)
        tasks.append((i, gens[i]))
    while tasks:
        i, gen = tasks.popleft()
        try:
            next(gen)
        except StopIteration as e:
            results[i] = e.value
            continue
        tasks.append((i, gen))
    return results
