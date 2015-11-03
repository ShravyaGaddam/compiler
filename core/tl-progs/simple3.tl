program
	var X as int ;
	var Y as int ;
begin
	X := readInt ;
	Y := readInt ;
	while X > Y do
		Y := Y + 1 ;
	end ;
	writeInt X * Y ;
end
