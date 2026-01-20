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

Parameter v_str5a : Any.
Parameter v_str5b : Any.
Parameter v_int7a : Any.
Parameter v_list_2_3 : Any.
Parameter v_int7b : Any.

Axiom NonInt_str5a : forall n, ~ IsInt v_str5a n.
Axiom NonInt_str5b : forall n, ~ IsInt v_str5b n.
Axiom IsInt_7a : IsInt v_int7a 7%Z.
Axiom NonInt_list_2_3 : forall n, ~ IsInt v_list_2_3 n.
Axiom IsInt_7b : IsInt v_int7b 7%Z.

Example test_case_new: filter_integers_spec [v_str5a; v_str5b; v_int7a; v_list_2_3; v_int7b] [7%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact NonInt_str5a.
  - eapply fir_cons_nonint.
    + exact NonInt_str5b.
    + eapply fir_cons_int.
      * exact IsInt_7a.
      * eapply fir_cons_nonint.
        -- exact NonInt_list_2_3.
        -- eapply fir_cons_int.
           ++ exact IsInt_7b.
           ++ constructor.
Qed.