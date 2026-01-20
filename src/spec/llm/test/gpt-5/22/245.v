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

Parameter inj_int : int -> Any.
Axiom IsInt_inj_int : forall n, IsInt (inj_int n) n.

Parameter v_one : Any.
Parameter v_list : Any.
Parameter v_dict : Any.

Axiom nonint_one : forall n, ~ IsInt v_one n.
Axiom nonint_list : forall n, ~ IsInt v_list n.
Axiom nonint_dict : forall n, ~ IsInt v_dict n.

Example test_case_mixed: filter_integers_spec [inj_int 89%Z; inj_int 1%Z; v_one; v_list; v_dict] [89%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_inj_int.
  - eapply fir_cons_int.
    + apply IsInt_inj_int.
    + eapply fir_cons_nonint.
      * apply nonint_one.
      * eapply fir_cons_nonint.
        -- apply nonint_list.
        -- eapply fir_cons_nonint.
           ++ apply nonint_dict.
           ++ constructor.
Qed.