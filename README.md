### Comparison of height and size based enumeration.

* 11604909.sl 

|  Program                                                                                        | # Examples |
|-------------------------------------------------------------------------------------------------|------------|
| Height - (str.substr (str.++ " " _arg_0) (str.indexof _arg_0 "." 1) (str.indexof _arg_0 " " 1)) | [3/6]      |           
| Size  -  (str.substr _arg_0 (+ -1 (str.indexof _arg_0 "." 1)) (str.len _arg_0))                 | [2/6]      |            
| Prob  -  ((str.substr _arg_0 (+ -1 (str.indexof _arg_0 "." 1)) (+ 1 (- 1 -1))) **[13s]**       | **[6/6]**   |             

* 30732554.sl

|  Program                                                                                        | # Examples |
|-------------------------------------------------------------------------------------------------|------------|
| Height - _arg_0                                                                                 | [2/4]      |
| Size  -  (str.substr _arg_0 0 (str.indexof (str.++ _arg_0  "\|") "\|" 1))                       | **[4/4]**  |
| Size  -  (str.substr _arg_0 0 (str.indexof (str.++ _arg_0  "\|") "\|" 1))  [2s]                 | **[4/4]**  |

* 38871714.sl

|  Program                                                                                        | # Examples Passed |
|-------------------------------------------------------------------------------------------------|-------------------|
| Height - (str.replace (str.replace _arg_0 "<" "") ">" "")                                       | [1/2]             |
| Size  -  (str.replace (str.replace _arg_0 "<" "") ">" "")                                       | [1/2]             |

* 39060015.sl 

|  Program                                                                                        | # Examples Passed |
|-------------------------------------------------------------------------------------------------|-------------------|
| Height - (ite (str.prefixof "/" _arg_0) "" _arg_0)                                              | [1/2]             |
| Size  -  (ite (str.prefixof "/" _arg_0) "" _arg_0)                                              | [1/2]             |

* 41503046.sl

|  Program                                                                                        | # Examples Passed |
|-------------------------------------------------------------------------------------------------|-------------------|
| Height - (str.substr _arg_0 0 (str.indexof _arg_0 " " 1))                                       | [4/6]             |                 
| Size  -  (str.substr _arg_0 0 (str.indexof _arg_0 " " (str.len (str.++ "ssp." "ssp."))))        | **[6/6]**         |                 
| Prob  -  (str.substr _arg_0 0 (str.indexof _arg_0 " " (str.len (str.++ "ssp." "ssp.")))) [1s]   | **[6/6]**         |    

* 43606446.sl

|  Program                                                                                                            |# Passed   |
|---------------------------------------------------------------------------------------------------------------------|-----------|
| Hgt - (str.++ (str.++ (str.at _arg_0 0) (str.at _arg_0 1)) (str.at (str.++ " " _arg_0) (str.indexof _arg_0 ">" 1)))| [1/4]      | 
| Size  -  (str.substr _arg_0 0 (+ -1 (+ -1 (str.indexof _arg_0 (str.at _arg_0 0) 1))))                              | [1/4]      |
| Prob  -  (str.substr _arg_0 (+ -1 (+ -1 (+ -1 (+ -1 (str.len _arg_0))))) (+ 1 (+ 1 1)))    **[64s]**               |**[4/4]**   |


* 44789427.sl

|  Program                                                                                                       | # Examples |
|----------------------------------------------------------------------------------------------------------------|------------|
| Height - (str.substr _arg_0 0 (str.indexof _arg_0 "-" _arg_1))                                                 | [2/4]      |                 
| Size  -  (str.substr _arg_0 0 (str.indexof _arg_0 "-" _arg_1))                                                 | [2/4]      | 
| Prob - ((str.substr _arg_0 (str.indexof (str.++ "-" _arg_0) "-" (+ _arg_1 -1)) (str.indexof _arg_0 "-" _arg_1))|[4/4] [20m] | 

* bikes.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (str.++ (str.at name 0) (str.replace (str.substr name 1 5) (int.to.str 1) (str.at " " 1))) | [4/6]    |                       
| Size  -  (str.substr name 0 (- (str.len name) 3))                                                   | **[6/6]**| 
| Size  -  (str.substr name 0 (- (str.len name) 3))  [2s]                                             | **[6/6]**| 

* count-total-words-in-a-cell.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (ite (str.contains (str.replace _arg_0 " " "") " ") (str.indexof _arg_0 " " 1) (+ 1 1))    | [2/3]    |                       
| Size  -  (+ 1 (- (str.to.int (str.++ (int.to.str 1) (int.to.str 1))) (str.indexof _arg_0 " " 1)))   | [2/3]    |                       
| Prob - ((+ -1 (+ -1 (+ -1 (+ (str.indexof _arg_0 " " 1) (str.to.int (str.at (int.to.str             | **[3/3]**|
|(str.indexof _arg_0 " " (+ 1 (str.indexof _arg_0 " " 1)))) 1))))))  [65s]                            |          |


* exceljet2.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (str.substr (str.replace _arg_0 "." _arg_0) (str.len _arg_0) (str.indexof _arg_0 "." 1))   | [1/3]    |                       
| Size  -  (str.substr _arg_0 (+ -1 (+ -1 (+ -1 (str.len _arg_0)))) (str.len _arg_0))                 | [2/3]    |    
| Prob - ((str.substr _arg_0 (+ 1 (str.indexof _arg_0 "." (+ -1 (+ -1 (+ -1 (str.len (str.substr      |**[3/3]** |
| _arg_0 1 (str.len (str.++ _arg_0 _arg_0))))))))) (str.len (str.++ _arg_0 _arg_0))) [11s]            |          |

* stackoverflow1.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (str.replace (str.replace _arg_0 "." "") (str.++ " " "Inc") "")                            | [2/3]    |                       
| Size  -  (str.substr _arg_0 0 (+ -1 (str.indexof _arg_0 "Inc" 1)))                                  | **[3/3]**|    

* stackoverflow2.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (str.substr _arg_0 0 (str.indexof _arg_0 " " 1))                                           | [1/2]    |                       
| Size  -  (str.substr _arg_0 0 (str.indexof _arg_0 " " (str.indexof _arg_0 "in" 1)))                 | **[2/2]**|
| Size  -  (str.substr _arg_0 0 (str.indexof _arg_0 " " (str.indexof _arg_0 "in" 1)))  [2s]           | **[2/2]**|

* stackoverflow3.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (ite (str.suffixof " " _arg_0) "" _arg_0)                                                  | [1/3]    |                       
| Size  -  (str.substr _arg_0 (- (str.to.int (str.++ "1" "9")) 2) (str.len _arg_0))                   | **[3/3]**|
| Size  -  (str.substr _arg_0 (- (str.to.int (str.++ "1" "9")) 2) (str.len _arg_0))    [12s]          | **[3/3]**|

* univ_2_short.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - (str.++ (str.++ col1 ",") (str.++ " " col2))                                               | [4/6]    |                       
| Size  -  (str.++ col1 (str.++ "," (str.++ " " col2)))                                               | [4/6]    |
 

* univ_3_short.sl

|  Program                                                                                            | # Passed |
|-----------------------------------------------------------------------------------------------------|----------|
| Height - col2                                                                                       | [4/6]    |                       
| Size  -  col2                                                                                       | [4/6]    |
