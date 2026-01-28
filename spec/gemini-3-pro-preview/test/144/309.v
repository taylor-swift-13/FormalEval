Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/13"; "857/7291"] -> x1=8, x2=13, n1=857, n2=7291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8 13 857 7291 false.
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
    (* We need to show false = true, derived from the contradiction in H_mod *)
    (* (8 * 857) mod (13 * 7291) evaluates to 6856 *)
    compute in H_mod.
    (* H_mod is now 6856 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.