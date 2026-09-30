import MegaDreifach.M9Canon

/-!
# M9 decoder checks, intermediate grips 20–29

Owns: the kernel checks `m9dec_20` … `m9dec_29` (one `decide!` per intermediate
grip `rotAt s1`, over all second cards `b < 52` and first cards `a < 52`; about 10 s
and 2 GB each).  Split across six files so that they build in parallel and no single
file runs long.  Collected in `M9.lean` (`dec_all`).
-/

namespace MegaDreifach.M9

open MegaDreifach.G2Cov

gen_m9_dec 20 30

end MegaDreifach.M9
