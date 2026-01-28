Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["943/9"; "943/9"] -> x1=943, x2=9, n1=943, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 943 9 943 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate (943 * 943) mod (9 * 9) *)
    (* This reduces to showing that a non-zero remainder equals 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.