Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163/58"; "2/252"] -> x1=163, x2=58, n1=2, n2=252
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 163 58 2 252 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate values: (163 * 2) mod (58 * 252) *)
    (* 163 * 2 = 326 *)
    (* 58 * 252 = 14616 *)
    (* 326 mod 14616 = 326 *)
    (* H_mod implies 326 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.