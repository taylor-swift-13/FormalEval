Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 : Any.
Axiom V1_nonint : forall n, ~ IsInt V1 n.
Axiom V3_nonint : forall n, ~ IsInt V3 n.
Axiom V4_nonint : forall n, ~ IsInt V4 n.
Axiom V5_nonint : forall n, ~ IsInt V5 n.
Axiom V6_nonint : forall n, ~ IsInt V6 n.
Axiom V7_nonint : forall n, ~ IsInt V7 n.
Axiom V9_nonint : forall n, ~ IsInt V9 n.
Axiom V10_nonint : forall n, ~ IsInt V10 n.
Axiom V11_nonint : forall n, ~ IsInt V11 n.
Axiom V2_isint : IsInt V2 2%Z.
Axiom V8_isint : IsInt V8 1%Z.

Example test_case_new: filter_integers_spec [V1; V2; V3; V4; V5; V6; V7; V8; V9; V10; V11] [2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply V1_nonint.
  - eapply fir_cons_int.
    + apply V2_isint.
    + eapply fir_cons_nonint.
      * apply V3_nonint.
      * eapply fir_cons_nonint.
        -- apply V4_nonint.
        -- eapply fir_cons_nonint.
           ++ apply V5_nonint.
           ++ eapply fir_cons_nonint.
              ** apply V6_nonint.
              ** eapply fir_cons_nonint.
                 --- apply V7_nonint.
                 --- eapply fir_cons_int.
                     +++ apply V8_isint.
                     +++ eapply fir_cons_nonint.
                         *** apply V9_nonint.
                         *** eapply fir_cons_nonint.
                             **** apply V10_nonint.
                             **** eapply fir_cons_nonint.
                                  ----- apply V11_nonint.
                                  ----- apply fir_nil.
Qed.