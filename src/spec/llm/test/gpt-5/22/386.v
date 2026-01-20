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

Parameter v2 v1 vone vlist vdict6a v5 vdict6b : Any.
Axiom IsInt_v2_2 : IsInt v2 2%Z.
Axiom IsInt_v1_1 : IsInt v1 1%Z.
Axiom NonInt_vone : forall n, ~ IsInt vone n.
Axiom NonInt_vlist : forall n, ~ IsInt vlist n.
Axiom NonInt_vdict6a : forall n, ~ IsInt vdict6a n.
Axiom IsInt_v5_5 : IsInt v5 5%Z.
Axiom NonInt_vdict6b : forall n, ~ IsInt vdict6b n.

Example test_case_mixed: filter_integers_spec [v2; v1; vone; vlist; vdict6a; v5; vdict6b] [2%Z; 1%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_v2_2.
  - eapply fir_cons_int.
    + exact IsInt_v1_1.
    + eapply fir_cons_nonint.
      * exact NonInt_vone.
      * eapply fir_cons_nonint.
        -- exact NonInt_vlist.
        -- eapply fir_cons_nonint.
           ++ exact NonInt_vdict6a.
           ++ eapply fir_cons_int.
              ** exact IsInt_v5_5.
              ** eapply fir_cons_nonint.
                 --- exact NonInt_vdict6b.
                 --- constructor.
Qed.