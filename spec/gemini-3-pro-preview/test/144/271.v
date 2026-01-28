Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4/136"; "468/136"] -> x1=4, x2=136, n1=468, n2=136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4 136 468 136 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (4 * 468) mod (136 * 136) *)
    (* 4 * 468 = 1872 *)
    (* 136 * 136 = 18496 *)
    (* 1872 mod 18496 = 1872 *)
    (* H_mod becomes 1872 = 0, a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.