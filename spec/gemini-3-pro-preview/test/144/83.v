Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1112/9"; "1112/9"] -> x1=1112, x2=9, n1=1112, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1112 9 1112 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res is false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (1112 * 1112) mod (9 * 9) *)
    (* 1112 * 1112 = 1236544 *)
    (* 9 * 9 = 81 *)
    (* 1236544 mod 81 = 79 *)
    (* H_mod becomes 79 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.