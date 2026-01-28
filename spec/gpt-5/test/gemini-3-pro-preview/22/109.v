Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive Any : Type :=
| AnyInt (i : Z)
| AnyString (s : string)
| AnyList (l : list Any).

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt i => n = i
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  destruct v; simpl in *; try contradiction.
  subst. reflexivity.
Qed.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [AnyInt 1%Z; 
     AnyList [AnyInt 2%Z; AnyString "3"]; 
     AnyList [AnyInt 4%Z]; 
     AnyList [AnyInt 5%Z; AnyInt 6%Z]; 
     AnyList [AnyInt 7%Z; AnyInt 8%Z]; 
     AnyInt 9%Z] 
    [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - simpl. reflexivity.
  - apply fir_cons_nonint.
    + intros n H. simpl in H. contradiction.
    + apply fir_cons_nonint.
      * intros n H. simpl in H. contradiction.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_nonint.
           ++ intros n H. simpl in H. contradiction.
           ++ apply fir_cons_int with (n := 9%Z).
              ** simpl. reflexivity.
              ** apply fir_nil.
Qed.