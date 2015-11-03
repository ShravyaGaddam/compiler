program
	var X as bool ;
	var Y as int ;
	var Z as int ;
begin
	X := readInt ;
	writeInt 2 * X ;
    if X = 2 then
	   X := 5 ;
	   Y := 6 * 7 * 8 + 5 ;
	   Z := 1 ;
	else
       X := 7 ;
    end ;   %  test a comment
end