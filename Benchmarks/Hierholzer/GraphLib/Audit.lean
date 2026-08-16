import Benchmarks.Hierholzer.GraphLib.Correctness
import Benchmarks.Hierholzer.GraphLib.Resource

/-!
# Kernel-axiom audit

This file is compiled separately so that the implementation report can preserve the kernel's
actual dependency lists for the principal representation, correctness, and resource theorems.
-/

open Benchmarks.Hierholzer.GraphLib

#print axioms representation_exists
#print axioms hierholzer_correct
#print axioms hierholzer_edgeless
#print axioms hierholzer_exact_length
#print axioms hierholzer_positive_edge_circuit
#print axioms hierholzer_component_bounds
#print axioms hierholzer_total_affine
#print axioms hierholzer_total_linear_mathematical
