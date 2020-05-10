; https=//exceljet.net/formula/get-first-name-from-name-with-comma
(set-logic SLIA)
(synth-fun f ((_arg_0 String) (_arg_1 Int)) String 
 ( (Start String (ntString)) 
 (ntString String (
	_arg_0
    " " "" "%" "(" ")" "+" "" "-" "." "/" "/n" "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "9999999" "<" "=" ">" "BRD" "Branding" "C0" "CA" "CT" "Company" "Corporation" "DRS" "Direct Response" "Dr." "Enterprises" "Inc" "LDS" "LLC" "Leads" "MD" "NY" "Name" "PA" "USA" "_" "_acme.com" "apple" "b" "bananas" "blue" "boo" "green" "in" "mac" "microsoft" "orange" "oranges" "other" "overhead" "pink" "some project" "ssp." "strawberries" "that" "windows" "yellow" "|"
	(str.++ ntString ntString) 
	(str.replace ntString ntString ntString) 
	(str.at ntString ntInt)
	(int.to.str ntInt)
	(ite ntBool ntString ntString)
	(str.substr ntString ntInt ntInt)
)) 
 (ntInt Int (
	_arg_1
	1 0 -1 1 2
	(+ ntInt ntInt)
	(- ntInt ntInt)
	(str.len ntString)
	(str.to.int ntString)
	(ite ntBool ntInt ntInt)
	(str.indexof ntString ntString ntInt)
)) 
 (ntBool Bool (
	
	true false
	(= ntInt ntInt)
	(str.prefixof ntString ntString)
	(str.suffixof ntString ntString)
	(str.contains ntString ntString)
)) ))
(constraint (= (f "Chang,Amy" 1) "Amy"))
(constraint (= (f "Chang,Amy" 2) "Chang"))
(constraint (= (f "smith,bobby" 2) "smith"))
(constraint (= (f "smith,bobby" 1) "bobby"))
(check-synth)
