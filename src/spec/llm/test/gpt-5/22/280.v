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

Parameters v_three1 v_int v_three2 v_list123 v_list45 v_six : Any.
Axiom nonint_three1 : forall n, ~ IsInt v_three1 n.
Axiom isint_v_int : IsInt v_int 1%Z.
Axiom nonint_three2 : forall n, ~ IsInt v_three2 n.
Axiom nonint_list123 : forall n, ~ IsInt v_list123 n.
Axiom nonint_list45 : forall n, ~ IsInt v_list45 n.
Axiom nonint_six : forall n, ~ IsInt v_six n.

Example test_case_new: filter_integers_spec [v_three1; v_int; v_three2; v_list123; v_list45; v_six] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact nonint_three1.
  - eapply fir_cons_int.
    + exact isint_v_int.
    + eapply fir_cons_nonint.
      * exact nonint_three2.
      * eapply fir_cons_nonint.
        -- exact nonint_list123.
        -- eapply fir_cons_nonint.
           ++ exact nonint_list45.
           ++ eapply fir_cons_nonint.
              ** exact nonint_six.
              ** constructor.
Qed.