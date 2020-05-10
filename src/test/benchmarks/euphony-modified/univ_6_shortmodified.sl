(set-logic SLIA)
(synth-fun f ((col1 String) (col2 String)) String
    ((Start String (ntString))
     (ntString String (col1 col2 " " "," "USA" "PA" "CT" "CA" "MD" "NY"  "New York"
(str.++ ntString ntString)
(str.replace ntString ntString ntString)
    " " "" "%" "(" ")" "+" "" "-" "." "/" "/n" "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "9999999" "<" "=" ">" "BRD" "Branding" "C0" "CA" "CT" "Company" "Corporation" "DRS" "Direct Response" "Dr." "Enterprises" "Inc" "LDS" "LLC" "Leads" "MD" "NY" "Name" "PA" "USA" "_" "_acme.com" "apple" "b" "bananas" "blue" "boo" "green" "in" "mac" "microsoft" "orange" "oranges" "other" "overhead" "pink" "some project" "ssp." "strawberries" "that" "windows" "yellow" "|"
(int.to.str ntInt)
(ite ntBool ntString ntString)
(str.substr ntString ntInt ntInt)
))
      (ntInt Int (0 1 2
(+ ntInt ntInt)
(- ntInt ntInt)
(str.len ntString)
(str.to.int ntString)
(str.indexof ntString ntString ntInt)
))
(ntBool Bool (true false
(= ntInt ntInt)
(str.prefixof ntString ntString)
(str.suffixof ntString ntString)
(str.contains ntString ntString)
))
))
(constraint (= (f "University of Pennsylvania" "Phialdelphia, PA, USA")
"Phialdelphia, PA, USA"))

(constraint (= (f "UCLA" "Los Angeles, CA")
"Los Angeles, CA, USA"))

(constraint (= (f "Cornell University" "Ithaca, New York, USA")
"Ithaca, NY, USA"))

(constraint (= (f "Penn" "Philadelphia, PA, USA")
"Philadelphia, PA, USA"))

(constraint (= (f "University of Maryland College Park" "College Park, MD")
"College Park, MD, USA"))

(constraint (= (f "University of Michigan" "Ann Arbor, MI, USA")
"Ann Arbor, MI, USA"))

(constraint (= (f "Columbia University" "New York, NY, USA")
"New York, NY, USA"))

(constraint (= (f "NYU" "New York, New York, USA")
"New York, NY, USA"))

(check-synth)
