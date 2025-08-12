`timescale 1ps/1ps


module tb_top #(
	parameter MASTER_FREQ = 100_000_000,
	parameter SLAVE_FREQ = 1_800_000,
    parameter SPI_MODE = 1,
    parameter SPI_TRF_BIT = 8
	)();

	logic clk;
	logic rst;
   	logic [1:0] req;
	logic [7:0] wait_duration;
	logic [(SPI_TRF_BIT-1):0] din_master;
	logic [(SPI_TRF_BIT-1):0] din_slave;
	logic [(SPI_TRF_BIT-1):0] dout_master;
	logic [(SPI_TRF_BIT-1):0] dout_slave;
	logic done_tx;
	logic done_rx;
	int bit_counter;	
	int sclk_senddata;	

    spi_top dut (.*);

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

  
    //Reset
    initial begin
        rst = 1;
        #15;
        rst = 0;
    end

    initial begin
        $display("Test start"); 
	$monitor("Time=%0t | rst=%0b | req=%0b |  din_master=%0b   |   dout_master=%0b |  din_slave=%0b | dout_slave=%0b  "  
		 ,$time,     rst,      req,       din_master,          dout_master ,      din_slave ,     dout_slave );  
            din_master = 0; 
            din_slave = 0;
	    req = 0;

        @(negedge rst);
            #10;
        // master send, slave received (mosi)
            req = 1;
            wait_duration = 10;
            din_slave = 0;
   
        repeat(2) begin
		din_master = 10010010;
            //din_master = $urandom_range(1000, 5000);
            @(posedge clk);
      

	//counter
	bit_counter=0;
	
        assign sclk_senddata= dut.spi_master_inst.sclk;
	while (bit_counter <= SPI_TRF_BIT) begin
		@(posedge sclk_senddata);
			bit_counter = bit_counter + 1;
			$display("bitcounter =%0d ", bit_counter);
		end
	
	 if (dout_slave === din_master)begin
			$display("--------PASS TEST--- dout_slave = din_master " );
		end else begin
		$display("Failed");
		end
      	wait (done_tx == 1);
	end

////////////////////////////////////////////////////////////////////////////////////////	
 	
          //slave send, master received (miso)
        #20;
        req = 2;
        din_master = 0;

        repeat(2) begin
            din_slave = $urandom_range(6000, 8000);
            @(posedge clk);
            wait (done_rx == 1);
        end 

            // full duplex
         #20;
        req = 3;

        repeat(2) begin
            din_slave = $urandom_range(6000, 8000);
            din_master = $urandom_range(1000, 5000);

            @(posedge clk);
            wait (done_rx == 1);
            wait (done_tx == 1);
        end 

        $display("Test complete.");
        $finish;
    end

    initial begin
        $fsdbDumpfile("spi_tb.fsdb");
        $fsdbDumpvars(0, tb_top, "+all");
    end
/*
     // Assertion
     property chk_dout_slave;
        @(posedge sclk) disable iff (req != 1)
        `
        
           
    endproperty


  ASST_CHK_DOUT_SLAVE: assert property (chk_dout_slave);
*/
endmodule

    
