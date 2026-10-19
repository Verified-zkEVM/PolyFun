"""Bounded PTY conversations shared by the two recurring example CLI test drivers."""
import os
import selectors
import subprocess
import time


def conversation(argv, exchanges, timeout=10):
    """Wait for each flushed prompt before sending its answer; always reap the child."""
    master, slave = os.openpty()
    process = None
    output = bytearray()
    pending = bytearray()
    try:
        process = subprocess.Popen(list(map(str, argv)), stdin=slave, stdout=slave, stderr=slave)
        os.close(slave)
        slave = None
        with selectors.DefaultSelector() as selector:
            selector.register(master, selectors.EVENT_READ)
            for prompt, answer in exchanges:
                expected = prompt.encode()
                deadline = time.monotonic() + timeout
                while expected not in pending:
                    if not selector.select(max(0, deadline - time.monotonic())):
                        raise TimeoutError(f"PTY waiting for {prompt!r}; received {output!r}")
                    try:
                        chunk = os.read(master, 4096)
                    except OSError as error:
                        raise AssertionError(f"PTY closed before {prompt!r}: {output!r}") from error
                    if not chunk:
                        raise AssertionError(f"PTY EOF before {prompt!r}: {output!r}")
                    output.extend(chunk)
                    pending.extend(chunk)
                end = pending.index(expected) + len(expected)
                del pending[:end]
                os.write(master, (answer + "\n").encode())
        assert process.wait(timeout=timeout) == 0, output
        return output.decode()
    finally:
        if process is not None:
            if process.poll() is None:
                process.kill()
            process.wait(timeout=5)
        os.close(master)
        if slave is not None:
            os.close(slave)
