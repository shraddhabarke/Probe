; https=//exceljet.net/formula/remove-leading-and-trailing-spaces-from-text
; (str.++ (ite (str.prefixof " " _arg_0) "" (str.at _arg_0 0)) (str.substr (str.replace (str.replace (str.replace (str.replace (str.replace _arg_0 (str.++ " " " ") " ") (str.++ " " " ") " ") (str.++ " " " ") " ") (str.++ " " " ") " ") (str.++ " " " ") " ") 1 (str.len _arg_0)))
(set-logic SLIA)
(synth-fun f ((_arg_0 String)) String 
 ( (Start String (ntString)) 
 (ntString String (
"" " " "BRD" "DRS" "LDS" "Branding" "Direct Response" "Leads" "=" "/" "in" "_" "9" "." "microsoft" "windows" "apple" "mac" "-" "1" "2" "3" "4" "5" "6" "7" "8" "0" "," "<" ">" "/n" "%" "b" "apple" "bananas" "strawberries" "oranges" "LLC" "Inc" "Corporation" "Enterprises" "Company" "(" ")" "+" "name" ","
	"" " "
	(str.++ ntString ntString) 
	(str.replace ntString ntString ntString) 
	(str.at ntString ntInt)
	(int.to.str ntInt)
	(ite ntBool ntString ntString)
	(str.substr ntString ntInt ntInt)
)) 
 (ntInt Int (	
	-1 1 2 3 4 5 6 7 8 9 0
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
(constraint (= (f "  The shawshank") "The shawshank"))
(constraint (= (f "The    godfather") "The godfather"))
(constraint (= (f "    pulp   fiction") "pulp fiction"))
(check-synth)
