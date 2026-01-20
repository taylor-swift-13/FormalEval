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

Parameter z0 z2 z4 z61 : int.
Notation "0%Z" := z0.
Notation "2%Z" := z2.
Notation "4%Z" := z4.
Notation "61%Z" := z61.

Parameter a0 a2 a3 a4 alist a61 aset atrue adict afalse : Any.
Axiom IsInt_a0 : IsInt a0 0%Z.
Axiom IsInt_a2 : IsInt a2 2%Z.
Axiom IsInt_a4 : IsInt a4 4%Z.
Axiom IsInt_a61 : IsInt a61 61%Z.
Axiom NonInt_a3 : forall n, ~ IsInt a3 n.
Axiom NonInt_alist : forall n, ~ IsInt alist n.
Axiom NonInt_aset : forall n, ~ IsInt aset n.
Axiom NonInt_atrue : forall n, ~ IsInt atrue n.
Axiom NonInt_adict : forall n, ~ IsInt adict n.
Axiom NonInt_afalse : forall n, ~ IsInt afalse n.

Example test_case_complex:
  filter_integers_spec [a0; a2; a3; a4; alist; a61; aset; atrue; adict; afalse]
                       [0%Z; 2%Z; 4%Z; 61%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_a0.
  - eapply fir_cons_int.
    + exact IsInt_a2.
    + eapply fir_cons_nonint.
      * intros n; apply NonInt_a3.
      * eapply fir_cons_int.
        -- exact IsInt_a4.
        -- eapply fir_cons_nonint.
           ++ intros n; apply NonInt_alist.
           ++ eapply fir_cons_int.
              ** exact IsInt_a61.
              ** eapply fir_cons_nonint.
                 --- intros n; apply NonInt_aset.
                 --- eapply fir_cons_nonint.
                     +++ intros n; apply NonInt_atrue.
                     +++ eapply fir_cons_nonint.
                         **** intros n; apply NonInt_adict.
                         **** eapply fir_cons_nonint.
                             ----- intros n; apply NonInt_afalse.
                             ----- apply fir_nil.
Qed.