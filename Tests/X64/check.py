#!/usr/bin/env python3
"""Check GNU encoding agreement, native/model parity, and the SysV C ABI."""

import ctypes
import json
import platform
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def run(*args: str, cwd: Path = ROOT) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(f"{args[0]} failed ({result.returncode}):\n{result.stderr[:6000]}\n{result.stdout[:2000]}")
    return result.stdout


def assemble(source: Path, target: Path) -> None:
    run("as", "--64", "--fatal-warnings", "-o", str(target), str(source))


def text_bytes(obj: Path, target: Path) -> bytes:
    run("objcopy", "-j", ".text", "-O", "binary", str(obj), str(target))
    return target.read_bytes()


def check_encodings(directory: Path) -> None:
    obj = directory / "encodings.o"
    assemble(directory / "encodings.s", obj)
    data = text_bytes(obj, directory / "encodings.bin")
    symbols = {}
    for line in run("nm", "-n", "--defined-only", str(obj)).splitlines():
        address, _, name = line.split()
        symbols[name] = int(address, 16)
    expected = json.loads((directory / "encodings.json").read_text())
    failures = []
    for index, case in enumerate(expected):
        start = symbols[f"enc_{index}"]
        end = symbols[f"enc_{index + 1}"] if index + 1 < len(expected) else symbols["enc_end"]
        actual = data[start:end]
        wanted = bytes(case["bytes"])
        if actual != wanted:
            failures.append(f"#{index} {case['source']}: GNU {actual.hex()} != model {wanted.hex()}")
    if failures:
        raise AssertionError(f"{len(failures)} encoding mismatches:\n" + "\n".join(failures[:20]))
    print(f"PASS: {len(expected)} encodings agree byte-for-byte with GNU as")


def check_native(directory: Path) -> None:
    library = directory / "native.so"
    run("gcc", "-shared", "-fPIC", "-Wl,-z,noexecstack", "-o", str(library), str(directory / "native.s"))
    native = ctypes.CDLL(str(library))
    cases = json.loads((directory / "native.json").read_text())
    failures = []
    for index, case in enumerate(cases):
        for prefix in ("native", "encoded"):
            function = getattr(native, f"{prefix}_{index}")
            function.argtypes = [ctypes.POINTER(ctypes.c_uint64)]
            function.restype = None
            result = (ctypes.c_uint64 * 4)()
            function(result)
            observed = [*result[:3], result[3] & case["mask"]]
            expected = [case["rax"], case["rdx"], case["r8"], case["flags"]]
            if observed != expected:
                failures.append(f"{prefix} #{index} {case['code']}: {observed} != {expected}")
    if failures:
        raise AssertionError(f"{len(failures)} native mismatches:\n" + "\n".join(failures[:20]))
    print(f"PASS: {len(cases)} model cases agree with native execution of both emitted and encoded code")


def check_fixtures(directory: Path) -> None:
    obj = directory / "fixtures.o"
    linked = directory / "fixtures.elf"
    assemble(directory / "fixtures.s", obj)
    run("ld", "-e", "sum_to_n", "-o", str(linked), str(obj))
    actual = text_bytes(linked, directory / "fixtures.bin")
    if actual != (directory / "fixtures.expected").read_bytes():
        raise AssertionError("symbolic lowering disagrees with GNU assembly/linking")
    executable = directory / "abi-test"
    run("gcc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-o", str(executable),
        str(ROOT / "Tests/X64/Abi.c"), str(ROOT / "Tests/X64/Abi.s"),
        str(directory / "fixtures.s"), str(directory / "data.s"))
    print(run(str(executable)).strip())
    print("PASS: symbolic labels, relative branches/calls, and RIP-relative addresses match linked bytes")


def main() -> None:
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("native differential checks require Linux x86-64")
    for tool in ("lake", "as", "objcopy", "nm", "ld", "gcc"):
        if shutil.which(tool) is None:
            raise RuntimeError(f"required test tool is unavailable: {tool}")
    print(run("lake", "build").strip())
    run("lake", "env", "lean", "Tests/X64.lean")
    with tempfile.TemporaryDirectory(prefix="leanasm-x64-") as temporary:
        directory = Path(temporary)
        print(run("lake", "env", "lean", "--run", "Tests/X64/Generate.lean", str(directory)).strip())
        check_encodings(directory)
        check_native(directory)
        check_fixtures(directory)


if __name__ == "__main__":
    main()
