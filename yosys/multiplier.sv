// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
		   input 	 rst,
                   input 	 clk,
                   input [7:0] 	 in1,
                   input [7:0] 	 in2,
                   output [15:0] out
                  );
   reg [3:0]  stage = 0;
   reg [15:0] accumulator = 0;
   reg [7:0]  in1_shifted = 0;
   reg [15:0] in2_shifted = 0;


   // Logic for controlling the stage
   always @(posedge clk) 
     if (rst || stage == 9)
       stage <= 0;
     else
       stage <= stage + 1;
   
   // Logic for in1_shifted and in2_shifted
   always @(posedge clk) 
     if (rst) begin
        in1_shifted <= 0;
        in2_shifted <= 0;
     end else if (stage == 0) begin
        in1_shifted <= in1;
        in2_shifted <= in2;
     end else begin
        in1_shifted <= in1_shifted >> 1;
        in2_shifted <= in2_shifted << 1;
     end

   // Logic for the accumulator
   always @(posedge clk)
     if (rst || stage == 9) begin
	      accumulator <= 0;
     end else if (in1_shifted[0]) begin
        accumulator <= accumulator + in2_shifted;
     end

   // Output logic
   assign out = accumulator;


`ifdef FORMAL
   // Extra registers for Q10
   reg [7:0] cpin1; // "Copy on in1"
   reg [7:0] cpin2; // "Copy of in2"
   reg [7:0] din1; // "Completed bit of in1"

   always @(posedge clk) begin
      // Tight upper bound for value `out`
      // Unsigned multiplication --> (2^8 - 1)^2 = 65025
      assert (0 <= out && out <= 65025);

      // Value `stage` increments on each clock cycle
      // Excluding times where stage resets to 0
      assert property ((stage != 0) |-> (stage == $past(stage) + 1));

      // Main multiplier property
      assert property ((stage == 9) |-> out == $past(in1,9) * $past(in2,9));

      // Value `out` monotonically increases during execution
      // Excluding stage = 0 as no previous state can be observed
      assert property ((stage != 0) |-> ($past(out) <= out));

      // Fourth stage of computation implies accumulator holds in1 * in2[3:0]
      // Result of forth stage of computation is reflected in stage 5
      assert property ((stage == 5) |-> (accumulator == $past(in1[3:0],5) * $past(in2,5)));

      // Prove similar properties about the value of the accumulator in the other stages
      // Accumulator needs to be 0 at the start, otherwise result will be incorrect
      assert property ((stage == 0) |-> (accumulator == 0));
      assert property ((stage == 1) |-> (accumulator == 0));
      assert property ((stage == 2) |-> (accumulator == $past(in1[0],2) * $past(in2,2)));
      assert property ((stage == 3) |-> (accumulator == $past(in1[1:0],3) * $past(in2,3)));
      assert property ((stage == 4) |-> (accumulator == $past(in1[2:0],4) * $past(in2,4)));
      assert property ((stage == 6) |-> (accumulator == $past(in1[4:0],6) * $past(in2,6)));
      assert property ((stage == 7) |-> (accumulator == $past(in1[5:0],7) * $past(in2,7)));
      assert property ((stage == 8) |-> (accumulator == $past(in1[6:0],8) * $past(in2,8)));
      assert property ((stage == 9) |-> (accumulator == $past(in1[7:0],9) * $past(in2,9)));

      // Prove that in1_shifted always holds the initial value of in1, shifted right by stage bits
      assert property ((stage == 0) |-> (in1_shifted == 0));
      assert property ((stage == 1) |-> (in1_shifted == $past(in1,1) >> (stage-1)));
      assert property ((stage == 2) |-> (in1_shifted == $past(in1,2) >> (stage-1)));
      assert property ((stage == 3) |-> (in1_shifted == $past(in1,3) >> (stage-1)));
      assert property ((stage == 4) |-> (in1_shifted == $past(in1,4) >> (stage-1)));
      assert property ((stage == 5) |-> (in1_shifted == $past(in1,5) >> (stage-1)));
      assert property ((stage == 6) |-> (in1_shifted == $past(in1,6) >> (stage-1)));
      assert property ((stage == 7) |-> (in1_shifted == $past(in1,7) >> (stage-1)));
      assert property ((stage == 8) |-> (in1_shifted == $past(in1,8) >> (stage-1)));
      assert property ((stage == 9) |-> (in1_shifted == $past(in1,9) >> (stage-1)));

      // Prove that in2_shifted always holds the initial value of in2, shifted left by stage bits
      // Impossible to say something from stage 0 since it will be a leftover result, plus we do not care
      assert property ((stage == 1) |-> (in2_shifted == $past(in2,1) << (stage-1)));
      assert property ((stage == 2) |-> (in2_shifted == $past(in2,2) << (stage-1)));
      assert property ((stage == 3) |-> (in2_shifted == $past(in2,3) << (stage-1)));
      assert property ((stage == 4) |-> (in2_shifted == $past(in2,4) << (stage-1)));
      assert property ((stage == 5) |-> (in2_shifted == $past(in2,5) << (stage-1)));
      assert property ((stage == 6) |-> (in2_shifted == $past(in2,6) << (stage-1)));
      assert property ((stage == 7) |-> (in2_shifted == $past(in2,7) << (stage-1)));
      assert property ((stage == 8) |-> (in2_shifted == $past(in2,8) << (stage-1)));
      assert property ((stage == 9) |-> (in2_shifted == $past(in2,9) << (stage-1)));

      // Use a cover statement to prove that 13 is a prime number
      // If the cover statement of "there exist a pair of inputs other than (1,13) that will produce 13" fails
      // Then we have proven that 13 is a prime number
      cover ((stage == 9) && !($past(in1,9) == 1 && $past(in2,9) == 13) && !($past(in1,9) == 13 && $past(in2,9) == 11) && (out == 13));

      // Combining properties in Q5 and Q6 into a single property
      // Set up registers to "remember the input": cpinx = $past(inx,stage)
      if (rst || stage == 0) begin
        cpin1 <= in1;
        cpin2 <= in2;
      end
      // Set up register to track the "completed bits of in1": din1 == cpin1[(stage-2):0]
      if (rst || stage == 0) din1 <= 0;
      else din1 <= din1 + ((cpin1[stage-1]) << (stage-1));
      // Assert that at any non-initial stage, accumulator must be the same as the "done bits of in1" * "in2"
      assert property ((stage != 0 && stage != 1) |-> (accumulator == din1 * cpin2));
   end
`endif

endmodule
