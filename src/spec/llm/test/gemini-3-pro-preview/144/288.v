Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["37/55"; "3/8"] -> x1=37, x2=55, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 37 55 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (37 * 3) mod (55 * 8) *)
    (* 37 * 3 = 111 *)
    (* 55 * 8 = 440 *)
    (* 111 mod 440 = 111 *)
    (* H_mod implies 111 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.