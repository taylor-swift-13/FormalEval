Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  ((exists n : Z, IZR n = x) /\ 
   (exists n : Z, IZR n = y) /\ 
   (exists n : Z, IZR n = z) /\
   (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-122.24385010385771) (-123.7) (-85.81130743495204) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [_ [[n Hn] _]].
    apply (f_equal (fun v => v * 10)) in Hn.
    replace (-123.7 * 10) with (IZR (-1237)) in Hn by lra.
    replace (IZR n * 10) with (IZR (n * 10)) in Hn by (rewrite mult_IZR; f_equal; lra).
    apply eq_IZR in Hn.
    lia.
Qed.