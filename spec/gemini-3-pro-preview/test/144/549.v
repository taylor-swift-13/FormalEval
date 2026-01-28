Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9999/01"; "7/25"] -> x1=9999, x2=1, n1=7, n2=25
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9999 1 7 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (9999 * 7) mod (1 * 25) *)
    (* 9999 * 7 = 69993 *)
    (* 1 * 25 = 25 *)
    (* 69993 mod 25 = 18 *)
    compute in H_mod.
    (* H_mod is now 18 = 0, which is a contradiction *)
    discriminate.
Qed.