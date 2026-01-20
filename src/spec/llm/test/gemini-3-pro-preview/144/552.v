Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/25"; "4767/736"] -> x1=7, x2=25, n1=4767, n2=736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 25 4767 736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (7 * 4767) mod (25 * 736) *)
    (* 7 * 4767 = 33369 *)
    (* 25 * 736 = 18400 *)
    (* 33369 mod 18400 = 14969 *)
    (* H_mod states 14969 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.