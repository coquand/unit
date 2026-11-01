#!/usr/bin/env python3
"""Compare full checking with --each and the incremental file server."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
import time
from run import ROOT, run


class Server:
    def __init__(self, checker, root):
        self.root = root
        self.state = root/"server"
        self.state.mkdir()
        self.log = (root/"server.log").open("w")
        self.process = subprocess.Popen([str(checker), str(root/"All.seg"),
                                         "--serve", str(self.state)],
                                        stdout=self.log, stderr=self.log)
        self.index = 0

    def request(self, command):
        self.index += 1
        name = str(self.index)
        pending = self.state/("req."+name+".tmp")
        pending.write_text(command+"\n")
        pending.rename(self.state/("req."+name))
        response = self.state/("resp."+name)
        deadline = time.monotonic()+5
        while not response.exists():
            if self.process.poll() is not None:
                raise RuntimeError("server exited: "+(self.root/"server.log").read_text())
            if time.monotonic() > deadline:
                raise RuntimeError("server timed out on "+command)
            time.sleep(.02)
        return response.read_text()

    def close(self):
        self.process.terminate()
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait(timeout=2)
        self.log.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", type=Path)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    checker = args.checker or Path(subprocess.check_output(
        ["cabal", "list-bin", "exe:seg"], cwd=ROOT, text=True).strip())
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix="unit-driver-audit-") as tmp:
        for name in ["each-root", "changed-first-root", "changed-root-dependent", "import-line-edit", "changed-lock"]:
            root = Path(tmp)/name
            root.mkdir()
            (root/"A.seg").write_text("data N = z ;\nv : N = z ;\n")
            (root/"All.seg").write_text("import A ;\ntest : A.N = A.v ;\n")
            if name in ["each-root", "changed-first-root"]:
                (root/"All.seg").write_text("import A ;\ndata Empty = ;\ncontradiction : Empty = A.v ;\n")
            if name == "import-line-edit":
                (root/"B.seg").write_text("data N = z ;\ndata Empty = ;\n")
                (root/"A.seg").write_text("import B ; v : B.N = z ;\n")
                (root/"All.seg").write_text("import A ;\n")
            if name == "changed-lock":
                (root/"B.seg").write_text("transparent A.v ;\n")
                (root/"C.seg").write_text("test : Id A.N A.v z = refl z ;\n")
                (root/"All.seg").write_text("import A ; import B ; import C ;\n")
            before = {p.name:p.read_text() for p in root.glob("*.seg")}
            history = []
            if name == "each-root":
                alternative = run(checker, root/"All.seg", ["--each"])
            else:
                server = Server(checker, root)
                try:
                    if name != "changed-first-root":
                        history.append(server.request("all"))
                        assert history[-1].rstrip().endswith("OK"), history[-1]
                        if name == "changed-root-dependent":
                            (root/"A.seg").write_text("data N = z ;\ndata B = yes ;\nv : B = yes ;\n")
                        elif name == "changed-lock":
                            (root/"B.seg").write_text("opaque A.v ;\n")
                        else:
                            (root/"A.seg").write_text("import B ; v : B.Empty = z ;\n")
                    output = server.request("changed")
                    alternative = {"stdout":output, "accepted":output.rstrip().endswith("OK")}
                finally:
                    server.close()
            fresh = run(checker, root/"All.seg")
            assert "FAILED:" in fresh["stdout"], fresh
            row = {"name":name, "before":before,
                   "after":{p.name:p.read_text() for p in root.glob("*.seg")},
                   "history":history, "alternative":alternative, "fresh":fresh,
                   "match":alternative["accepted"] == fresh["accepted"]}
            rows.append(row)
            print(name, "PASS" if row["match"] else "MISMATCH", flush=True)
    (args.out/"driver-results.json").write_text(json.dumps(rows, indent=2))
    raise SystemExit(1 if any(not row["match"] for row in rows) else 0)


if __name__ == "__main__":
    main()
