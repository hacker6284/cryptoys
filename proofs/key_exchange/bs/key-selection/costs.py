"""Cost per key bit of two candidate keys that were not chosen (NOTES.md): the free fleet alone
(fleet walk + grow-until-it-bumps build) and pegs-only.  Run from this directory; reads the
ships-pegs build statistics and DP results."""
import json, math, os
SP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ships-pegs")
sim = json.load(open(os.path.join(SP, "sim_bump_results.json")))
rules = {}
for f in ["rules_len_grow_grow2_pow.json", "rules_grow_w_pow_w.json",
          "rules_bump_turn_bump_reroll_grow_turn.json", "rules_br_2_6_3_br_2_3_6_br_3_6_6.json"]:
    for r in json.load(open(os.path.join(SP, f))): rules[r["key"]] = r
R = rules["bump_reroll"]
H, H2, Hm = R["H"], R["H2"], R["Hmin"]
cells, hits = sim["cells"], sim["hit_units"]
PEG_H = 100 * math.log2(3)
def fleet_mults(G): return G * (4 * cells + hits) + 1          # 2 walks x cube(2) per cell + shared hits + check
def peg_mults(G): return 500 * G - 5.5                          # BS §7 formula
out = {"per_grid": {
    "fleet": {"mults": fleet_mults(1), "H": H, "H2": H2, "Hmin": Hm, "cells": cells, "hit_units": hits,
              "mults_per_H_bit": fleet_mults(1) / H, "mults_per_Hmin_bit": fleet_mults(1) / Hm,
              "public_mults_per_bit": 2 * cells / H},
    "pegs": {"mults": peg_mults(1), "H": PEG_H, "mults_per_bit": peg_mults(1) / PEG_H,
             "public_mults_per_bit": 2 * 98.5 / PEG_H}}}
out["ratio_H"] = out["per_grid"]["fleet"]["mults_per_H_bit"] / out["per_grid"]["pegs"]["mults_per_bit"]
out["ratio_H2"] = (fleet_mults(1) / H2) / out["per_grid"]["pegs"]["mults_per_bit"]
out["ratio_Hmin"] = out["per_grid"]["fleet"]["mults_per_Hmin_bit"] / out["per_grid"]["pegs"]["mults_per_bit"]
mpm = {"R1024": 7.45e5, "R2048": 2.97e6, "R3072": 6.62e6, "R7680": 4.14e7, "R15360": 1.66e8}
sec = {"R1024": 80, "R2048": 112, "R3072": 128, "R7680": 192, "R15360": 256}
tiers = []
for t, s in sec.items():
    gp = math.ceil(s / (PEG_H / 2)); gH = math.ceil(s / (H / 2)); gM = math.ceil(s / (Hm / 2))
    tiers.append({"tier": t, "security": s, "pegs_grids": gp, "pegs_mults": peg_mults(gp), "pegs_moves": peg_mults(gp) * mpm[t],
                  "fleet_grids_H": gH, "fleet_mults_H": fleet_mults(gH), "fleet_moves_H": fleet_mults(gH) * mpm[t],
                  "fleet_grids_Hmin": gM, "fleet_mults_Hmin": fleet_mults(gM), "fleet_moves_Hmin": fleet_mults(gM) * mpm[t]})
out["tiers"] = tiers
out["build"] = {"fleet_rolls": sim["rolls"], "fleet_piece_moves": sim["piece_moves"], "fleet_miss_pegs": sim["miss_pegs"],
                "pegs_rolls": 100, "pegs_pegs_placed": 200 / 3}
# ECBS: additions = nonzero cells, Frobenius = cells
out["ecbs"] = {"fleet_nonzero_cells": sim["nonzero_cells"], "fleet_adds_per_Hbit": sim["nonzero_cells"] / H,
               "pegs_adds_per_bit": (200 / 3) / PEG_H}
out["sub_eq_cruiser_variant"] = {"H": H - sim["kinds"]["S"] - sim["kinds"]["C"], "cells": 100,
                                 "mults": 400 + hits - sim["kinds"]["C"] + 1}
out["sub_eq_cruiser_variant"]["ratio_H"] = (out["sub_eq_cruiser_variant"]["mults"] / out["sub_eq_cruiser_variant"]["H"]) / (peg_mults(1) / PEG_H)
out["uniform_restart"] = {"x": 0.31291, "log2_acceptance": 150.187464 + 100 * math.log2(0.31291),
                          "x_5_16_log2_acceptance": 150.187464 + 100 * math.log2(5 / 16)}
print(json.dumps(out, indent=1))
json.dump(out, open("costs_results.json", "w"), indent=1)
