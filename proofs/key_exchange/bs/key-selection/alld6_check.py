"""The dropped all-d6 layout (alld6.py) against the exact model, by the checks of
../ships-pegs/keygrid_check.py (chi-square on 2x2, 2x3, 3x2, 1x5, 5x1; 20,000 10x10 builds).
Analysis only (NOTES.md §5).

These runs used to follow the SPEC-dice runs in keygrid_check.py on one random stream (seed
2027).  To keep the recorded figures, this script first replays those SPEC-dice runs on the same
stream and discards them, then runs the all-d6 layout.

  python3 alld6_check.py > alld6_check_results.txt      # writes alld6_check_results.json
"""
import io, json, random, sys, contextlib
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "ships-pegs"))
import keygrid, keygrid_check
from alld6 import build_all_d6


def main():
    rng = random.Random(2027)
    with contextlib.redirect_stdout(io.StringIO()):     # replay the SPEC-dice runs, discarded
        keygrid_check.run_set(rng, keygrid.build, "d12+cup", {"small": {}, "10x10": {}})
    out = {"small": {}, "10x10": {}}
    keygrid_check.run_set(rng, build_all_d6, "d6", out)
    json.dump(out, open(HERE / "alld6_check_results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
