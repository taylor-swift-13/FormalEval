Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Definition int := Z.
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

Parameter a0 a1 a2 a3 a4 a5 : Any.
Axiom IsInt_a0 : IsInt a0 0%Z.
Axiom NonInt_a1 : forall n, ~ IsInt a1 n.
Axiom NonInt_a2 : forall n, ~ IsInt a2 n.
Axiom NonInt_a3 : forall n, ~ IsInt a3 n.
Axiom NonInt_a4 : forall n, ~ IsInt a4 n.
Axiom NonInt_a5 : forall n, ~ IsInt a5 n.

Example test_case_mixed: filter_integers_spec [a0; a1; a2; a3; a4; a5] [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_a0.
  - eapply fir_cons_nonint.
    + apply NonInt_a1.
    + eapply fir_cons_nonint.
      * apply NonInt_a2.
      * eapply fir_cons_nonint.
        -- apply NonInt_a3.
        -- eapply fir_cons_nonint.
           ++ apply NonInt_a4.
           ++ eapply fir_cons_nonint.
              ** apply NonInt_a5.
              ** constructor.
Qed.