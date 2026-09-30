import MegaDreifach.M9Canon

/-!
# M9 decoder checks, intermediate grips 30–39

Owns: the kernel checks `m9dec_30` … `m9dec_39` (one `decide!` per intermediate
grip `rotAt s1`, over all second cards `b < 52` and first cards `a < 52`; about 10 s
and 2 GB each, local, single process).  Split across six files so that they build in
parallel and no single file runs long.  In CI the six files take about 4.3 min wall
together, built 4 in parallel; CI does not measure memory.  Collected in `M9.lean` (`dec_all`).
-/

namespace MegaDreifach.M9

open MegaDreifach.G2Cov

gen_m9_dec 30 40

end MegaDreifach.M9
