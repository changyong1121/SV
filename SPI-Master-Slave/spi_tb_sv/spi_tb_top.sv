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
        $display("Test start.");     
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
            din_master = $urandom_range(1000, 5000);
            //din_slave = $urandom_range(11, 20);
            @(posedge clk);
            wait (done_tx == 1);
        end 

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

        repeat(100) begin
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

    
