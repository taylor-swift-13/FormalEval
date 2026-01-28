Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["857/2991"; "8/13"] -> x1=857, x2=2991, n1=8, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 857 2991 8 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (857 * 8) mod (2991 * 13) *)
    (* 6856 mod 38883 = 6856 *)
    (* H_mod becomes 6856 = 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.