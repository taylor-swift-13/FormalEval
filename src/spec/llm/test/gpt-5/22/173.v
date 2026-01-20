Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Require Import Coq.ZArith.ZArith.

Parameter inj : Z -> int.

Parameter v1 v4 v5 v7 v9 v5' : Any.
Axiom v1_is_int : IsInt v1 (inj 1%Z).
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v9_is_int : IsInt v9 (inj 9%Z).
Axiom v5'_nonint : forall n, ~ IsInt v5' n.

Example test_case_new: filter_integers_spec [v1; v4; v5; v7; v9; v5'] [inj 1%Z; inj 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply v1_is_int.
  - eapply fir_cons_nonint.
    + apply v4_nonint.
    + eapply fir_cons_nonint.
      * apply v5_nonint.
      * eapply fir_cons_nonint.
        { apply v7_nonint. }
        { eapply fir_cons_int.
          - apply v9_is_int.
          - eapply fir_cons_nonint.
            + apply v5'_nonint.
            + constructor. }
Qed.