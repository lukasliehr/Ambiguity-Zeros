"""Check that the theorems proved in Showcase_WithProofs.lean have exactly the
statements of Showcase.lean and depend only on Lean's standard axioms.

Run from anywhere with `python3 scripts/check_completion.py`.
"""

from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
targets = [
    "AmbiguityHoles.bounded_openZeros_phaseRetrieval",
    "AmbiguityHoles.prescribed_openZeros",
    "AmbiguityHoles.forbidden_annulus",
]
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
showcase = (root / "Showcase.lean").read_text()
source = (
    "import Showcase_WithProofs\n"
    "set_option linter.unusedVariables false\n"
    "noncomputable section\nopen MeasureTheory\nnamespace ShowcaseConsistency\n"
)
for definition in ["Rd", "L2", "PhaseSpace", "ambiguity", "openZeros", "stft", "DoesPhaseRetrieval", "annulus"]:
    match = re.search(
        rf"(?:abbrev|def) {re.escape(definition)}\b.*?(?=\n(?:abbrev|def) |\n\n|\nend)", showcase, re.S
    )
    if match is None:
        raise SystemExit(f"Could not read Showcase definition {definition}.")
    source += match[0] + "\n\n"
for name in targets:
    short_name = name.rsplit(".", 1)[1]
    match = re.search(
        rf"theorem {re.escape(short_name)}\b(.*?)\s*:=\s*by", showcase, re.S
    )
    if match is None:
        raise SystemExit(f"Could not read the Showcase signature of {name}.")
    # Each Showcase declaration puts its conclusion after a colon and newline.
    binders, conclusion = re.split(r"\s*:\s*\n", match[1], maxsplit=1)
    expected_type = (
        f"∀ {binders.strip()},\n{conclusion}" if binders.strip() else conclusion
    )
    source += f"example : {expected_type} := @{name}\n#print axioms {name}\n"
source += "end ShowcaseConsistency\n"

if subprocess.run(["lake", "build", "Showcase_WithProofs"], cwd=root).returncode:
    raise SystemExit("Building Showcase_WithProofs failed.")

with tempfile.TemporaryDirectory() as directory:
    check = Path(directory) / "Completion.lean"
    check.write_text(source)
    result = subprocess.run(
        ["lake", "env", "lean", str(check)], cwd=root,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )

print(result.stdout, end="")
if result.returncode:
    raise SystemExit("Verification failed; inspect the Lean diagnostics above.")

for name in targets:
    match = re.search(
        rf"'{re.escape(name)}' depends on axioms:\s*\[([^\]]*)\]", result.stdout
    )
    if match is None:
        raise SystemExit(f"Could not audit {name}.")
    axioms = {item.strip() for item in match[1].split(",") if item.strip()}
    if axioms - allowed_axioms:
        raise SystemExit(f"Unapproved axioms in {name}: {axioms - allowed_axioms}")

print("All three full statements have checked proofs using only standard axioms.")
