
Require Import List String Ascii.
Import ListNotations.

Definition split_words_spec (txt : string) (result : list string + nat) : Prop :=
  (exists ws, In ws (map (fun c => String c "") [' '; Ascii.LF; Ascii.CR; Ascii.Tab]) /\ 
              In ws (map (fun c => String c "") (list_ascii_of_string txt))) \/
  (exists comma, In comma (map (fun c => String c "") [", "]) /\ 
                In comma (map (fun c => String c "") (list_ascii_of_string txt))) \/
  (~(exists ws, In ws (map (fun c => String c "") [' '; Ascii.LF; Ascii.CR; Ascii.Tab]) /\ 
               In ws (map (fun c => String c "") (list_ascii_of_string txt))) /\
   ~(exists comma, In comma (map (fun c => String c "") [", "]) /\ 
                  In comma (map (fun c => String c "") (list_ascii_of_string txt))) /\
   match result with
   | inl words => False
   | inr count => count = length (filter (fun ch => 
                        is_lower ch /\ Z.odd (Z.of_nat (ascii_to_nat ch - ascii_to_nat "a"%char))) 
                        (list_ascii_of_string txt))
   end).
