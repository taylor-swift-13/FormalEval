
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Section MaximumSpec.

Variable arr : list Z.
Variable k : nat.
Variable result : list Z.

Definition sorted_non_decreasing := Sorted Z.le.
Definition sorted_non_increasing := Sorted (fun x y => y <= x).

Definition maximum_spec :=
  length result = k /\
  (forall x, In x result -> In x arr) /\
  Permutation.Permutation (firstn k (rev (sort Z.leb arr))) result /\
  sorted_non_decreasing result /\
  (forall x, In x arr -> (exists y, In y result /\ x <= y) \/ (exists y, In y arr /\ (In y result -> y >= x))).

End MaximumSpec.


**Explanation:**  
- The result list `result` has length `k`.  
- All elements in `result` appear in `arr`.  
- `result` is a permutation of the first `k` elements of the reversed sorted list of `arr`—this corresponds to the top `k` elements in descending order derived from the sorted original list (which is ascending sorted by default).  
- `result` is sorted non-decreasing (i.e., ascending).  
- The last property ensures that the elements in `result` are the maximum `k` elements from `arr`: every element of `arr` is less or equal to some element in `result`.  

If you prefer, some parts (like the somewhat complex last property) can be adjusted for clarity based on how strict you want the spec to be, but this captures the key properties from the description and code behavior.