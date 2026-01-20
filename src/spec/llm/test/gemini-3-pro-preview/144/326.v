Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4/1136"; "4/1136"] -> x1=4, x2=1136, n1=4, n2=1136
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4 1136 4 1136 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (4 * 4) mod (1136 * 1136) *)
    (* 16 mod 1290496 = 16 *)
    (* H_mod becomes 16 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.