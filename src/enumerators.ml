type term_types = Int of int

let show_value = function Int v -> string_of_int v
                                 
type enum_result = EnumInt of string * int
		 | EnumPair of enum_result * enum_result

module ParamEval = Map.Make(String);;

let rec make_eval = function EnumInt(x,v) -> ParamEval.singleton x (Int v)
                           | EnumPair(e,f) -> ParamEval.union (fun _ _ _ -> None) (make_eval e) (make_eval f)

let showEval eval = String.concat ", " (List.map (fun (x,v) -> x ^ "=" ^ show_value v) (ParamEval.bindings eval))

class virtual enumerator =
        object
	    method virtual get_name: string
            method virtual get: int -> enum_result option 
            method virtual is_infinite: bool
            method virtual how_many: int
          end

class emptyEnumerator =
          object
            inherit enumerator
	    method get_name = ""
            method is_infinite = false
            method get _ = None
            method how_many = 0
          end

class natEnumerator (x: string) (s: int) (t: int) (z: int option) =
object (self)
  inherit enumerator

  val infinite = match z with
      None -> true
    | _    -> false
  val last = match z with
      None -> -1
    | Some z' -> z'
               	      
  method get_name = x
  method is_infinite = infinite
  method get i = let n = s + i*t in
                 if infinite || n <= last then Some (EnumInt(x,n)) else None

  method how_many = if infinite then -1 else (last - s)/t + 1
                  
end;;

class finiteSetEnumerator (x: string) (es: int list) = 
object (self)
  inherit enumerator

  val elements = Array.of_list es

  method is_infinite = false
  method get_name = x
  method get i = if i < Array.length elements then Some (EnumInt(x,elements.(i))) else None
  method how_many = Array.length elements
end;;
  
class pairEnumerator (e1: enumerator) (e2: enumerator) =
object (self)
  inherit enumerator

        
  method get_name = e1#get_name ^ e2#get_name
  method is_infinite = e1#is_infinite || e2#is_infinite

  method private find_coordinates_inf_inf n = let s = ref 1 in
				              let z = ref n in
				              while !s <= !z do
					        z := !z - !s;
					        s := !s + 1
				              done;
				              s := !s - 1;
				              let y = !z in
				              let x = !s - y in
				              (x,y)

  method get i = if e1#is_infinite then
                   begin
                     if e2#is_infinite then
                       begin
                         let (ix,iy) = self#find_coordinates_inf_inf i in
                         match (e1#get ix, e2#get iy) with
                           (Some x, Some y) -> Some (EnumPair (x,y))
                         | _                -> failwith "enumerators.pairEnumerator.get: impossible case 1 detected!"
                       end                     else
                       begin
                         let ys = e2#how_many in
                         let ix = i / ys in
                         let iy = i mod ys in
                         match (e1#get ix, e2#get iy) with
                           (Some x, Some y) -> Some (EnumPair (x,y))
                         | _                -> failwith "enumerators.pairEnumerator.get: impossible case 2 detected!"
                       end
                   end
                 else
                   begin
                     if e2#is_infinite then
                       begin
                         let xs = e1#how_many in
                         let iy = i / xs in
                         let ix = i mod xs in
                         match (e1#get ix, e2#get iy) with
                           (Some x, Some y) -> Some (EnumPair (x,y))
                         | _                -> failwith "enumerators.pairEnumerator.get: impossible case 3 detected!"
                       end
                     else
                       begin
                         let ys = e2#how_many in
                         let ix = i / ys in
                         let iy = i mod ys in
                         match (e1#get ix, e2#get iy) with
                           (Some x, Some y) -> Some (EnumPair (x,y))
                         | (None, _)        -> None
                         | _                -> failwith "enumerators.pairEnumerator.get: impossible case 4 detected!"
                       end
                   end

  method how_many = if e1#is_infinite || e2#is_infinite then -1 else e1#how_many * e2#how_many

end;;


