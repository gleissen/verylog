module simple_race1(x,y,z);
   input x, y;
   output z;

   reg    tmp;
   reg    x;
   reg    y;
   reg    z;

   assign tmp = x;

   always @(*) begin
      if (x == 1)
        x = y;
      else
        z = x;
   end

   always @(*) begin
      z = y;
   end
endmodule
