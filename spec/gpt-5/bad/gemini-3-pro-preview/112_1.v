Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Open string_scope to allow using string literals like "abcde" *)
Open Scope string_scope.

Fixpoint rev_string_acc (s acc : string) : string :=
  match s with
  | String.EmptyString => acc
  | String.String ch rest => rev_string_acc rest (String.String ch acc)
  end.

Definition rev_string (s : string) : string :=
  rev_string_acc s String.EmptyString.

Inductive CharIn : ascii -> string -> Prop :=
| CharIn_here : forall ch rest, CharIn ch (String.String ch rest)
| CharIn_there : forall ch ch' rest, CharIn ch rest -> CharIn ch (String.String ch' rest).

Inductive Filtered : string -> string -> string -> Prop :=
| Filtered_nil : forall c, Filtered String.EmptyString c String.EmptyString
| Filtered_skip : forall ch s c ss, CharIn ch c -> Filtered s c ss -> Filtered (String.String ch s) c ss
| Filtered_keep : forall ch s c ss, ~ CharIn ch c -> Filtered s c ss -> Filtered (String.String ch s) c (String.String ch ss).

Definition reverse_delete_spec (s c : string) (out : string * bool) : Prop :=
  exists ss b,
    Filtered s c ss /\
    ((b = true /\ ss = rev_string ss) \/ (b = false /\ ss <> rev_string ss)) /\
    out = (ss, b).

Example test_reverse_delete : reverse_delete_spec "abcde" "ae" ("bcd", false).
Proof.
  unfold reverse_delete_spec.
  exists "bcd", false.
  split.
  - (* Prove Filtered "abcde" "ae" "bcd" *)
    apply Filtered_skip.
    + (* 'a' is in "ae" *)
      apply CharIn_here.
    + apply Filtered_keep.
      * (* 'b' is not in "ae" *)
        intro H. 
        inversion H as [|? ? ? H1]; subst.
        { (* 'b' = 'a' *) discriminate. }
        { (* 'b' in "e" *)
          inversion H1 as [|? ? ? H2]; subst.
          { (* 'b' = 'e' *) discriminate. }
          { (* 'b' in "" *) inversion H2. }
        }
      * apply Filtered_keep.
        -- (* 'c' is not in "ae" *)
           intro H. 
           inversion H as [|? ? ? H1]; subst.
           { discriminate. }
           { inversion H1 as [|? ? ? H2]; subst.
             { discriminate. }
             { inversion H2. }
           }
        -- apply Filtered_keep.
           ++ (* 'd' is not in "ae" *)
              intro H. 
              inversion H as [|? ? ? H1]; subst.
              { discriminate. }
              { inversion H1 as [|? ? ? H2]; subst.
                { discriminate. }
                { inversion H2. }
              }
           ++ apply Filtered_skip.
              ** (* 'e' is in "ae" *)
                 apply CharIn_there. apply CharIn_here.
              ** apply Filtered_nil.
  - split.
    + (* Prove output condition: b=false and not palindrome *)
      right. split.
      * reflexivity.
      * (* Prove "bcd" <> rev "bcd" *)
        unfold rev_string. simpl.
        intro H.
        (* "bcd" = "dcb" implies 'b'='d', which is false *)
        discriminate H.
    + (* Prove output equality *)
      reflexivity.
Qed.