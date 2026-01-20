Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter fromZ : Z -> Any.
Parameter fromString : string -> Any.
Parameter fromR : R -> Any.
Axiom IsInt_fromZ : forall z, IsInt (fromZ z) z.
Axiom IsInt_not_string : forall s n, ~ IsInt (fromString s) n.
Axiom IsInt_not_R : forall r n, ~ IsInt (fromR r) n.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_case_mixed: filter_integers_spec
  [fromZ 1%Z; fromZ 2%Z; fromZ 3%Z; fromString "four"; fromR 5.5%R; fromString "seven"; fromR 9.0%R; fromString "four"]
  [1%Z; 2%Z; 3%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_fromZ.
  - eapply fir_cons_int.
    + apply IsInt_fromZ.
    + eapply fir_cons_int.
      * apply IsInt_fromZ.
      * eapply fir_cons_nonint.
        { intros n. apply IsInt_not_string. }
        eapply fir_cons_nonint.
        { intros n. apply IsInt_not_R. }
        eapply fir_cons_nonint.
        { intros n. apply IsInt_not_string. }
        eapply fir_cons_nonint.
        { intros n. apply IsInt_not_R. }
        eapply fir_cons_nonint.
        { intros n. apply IsInt_not_string. }
        apply fir_nil.
Qed.