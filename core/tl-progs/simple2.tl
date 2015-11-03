program
	var X as int ;
	var Y as int ;
begin
    X := readInt ;
    Y := readInt ;
	if X > Y then
		writeInt 2 * X ;
	end ;
	writeInt X - Y ;
end
