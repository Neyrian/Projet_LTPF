(*function that will converts char '7' to integer 7 *)
let convert_char_int: char -> int =
  fun c -> (int_of_char c) - 48

(*function that will converts ['1';'2';'8'] to 128*)
let rec list_char_to_int: char list -> int -> int=
  fun l x ->
  match l with
  | y::l -> list_char_to_int l (x * 10 + (convert_char_int y))
  | [] -> x

(*Converts from string to a list of char*)
let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
  in boucle s 0 (String.length s)

