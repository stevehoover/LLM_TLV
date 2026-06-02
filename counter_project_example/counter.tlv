\m4_TLV_version 1d: tl-x.org
\SV
   module counter(
      input clk,
      input reset,
      output reg [7:0] count
   );
\TLV
   |count_pipe
      @1
         $count[7:0] = *reset ? 8'b0 : >>1$count + 8'b1;
         *count = >>1$count;
\SV
   endmodule
