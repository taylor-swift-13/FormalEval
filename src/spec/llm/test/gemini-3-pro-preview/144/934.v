Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["716/17"; "3380/41"] -> x1=716, x2=17, n1=3380, n2=41
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 716 17 3380 41 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (716 * 3380) mod (17 * 41) to show it is not 0 *)
    compute in H_mod.
    (* H_mod evaluates to 96 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.