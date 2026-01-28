Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["33/8"; "13/77"] -> x1=33, x2=8, n1=13, n2=77
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 33 8 13 77 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (33 * 13) mod (8 * 77) *)
    (* 33 * 13 = 429 *)
    (* 8 * 77 = 616 *)
    (* 429 mod 616 = 429 *)
    (* H_mod : 429 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.