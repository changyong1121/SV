//`timescale 1ns/ps

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
    logic [7:0] expected_dout_slave;
    logic [7:0] expected_dout_master;
    logic [3:0] slv_bit_received_count;     
    logic [3:0] mstr_bit_received_count; 
	logic sclk;
    logic sclk_posedge;
    logic sclk_negedge;
    logic cs;

	int bit_counter_mstr;	
	int bit_counter_slv;	    
	int sclk_senddata;	
   
    spi_top dut (.*);

    logic [1:0] mstr_state_tx;
    logic mstr_state_rx;
    logic slv_state_tx;
    logic slv_state_rx;

    assign mstr_state_tx = dut.spi_master_inst.state_tx[1:0];
    assign mstr_state_rx = dut.spi_master_inst.state_rx;
    assign slv_state_tx = dut.spi_slave_inst.state_tx;
    assign slv_state_rx = dut.spi_slave_inst.state_rx;
    assign sclk_senddata= dut.spi_master_inst.sclk;
    assign sclk = dut.sclk_generator_inst.sclk;
    assign sclk_posedge = dut.spi_master_inst.sclk_posedge;
    assign sclk_negedge = dut.spi_master_inst.sclk_negedge;
    assign cs = dut.spi_master_inst.cs;

	task check_dout_slv(); //req 01
	bit_counter_slv=0;
	while (bit_counter_slv < SPI_TRF_BIT) begin
		@(posedge sclk_negedge);
			bit_counter_slv = bit_counter_slv + 1;
			$display("--->data_slv_received_counter =%0d ", bit_counter_slv);
		end
	@(posedge sclk_negedge);  //assume it is setup stage
		if (bit_counter_slv==8) begin
	 		if (dout_slave === din_master)begin
			$display("---------------------------------------PASS TEST--REQ=2'01--MOSI--dout_slave = din_master -----------------------------------------  " );
			end 
		end	else begin
		$display("Failed");
		end
	endtask


	task check_dout_mstr(); //req 10
	bit_counter_mstr=0;
	while (bit_counter_mstr < SPI_TRF_BIT) begin
		@(posedge sclk_negedge);
			bit_counter_mstr = bit_counter_mstr + 1;
			$display("--->data_mstr_received_counter =%0d ", bit_counter_mstr);
		end
	@(posedge sclk_negedge);  //assume it is setup stage
		if (bit_counter_mstr == 8) begin
	 		if (dout_master === din_slave)begin
			$display("---------------------------------------PASS TEST--REQ=2'10--MISO--dout_master = din_slave----------------------------------------- " );
			end 
		end	else begin
		$display("Failed");
		end
	endtask





    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

  
    //Reset
    initial begin
        $display("Test start.");     
        $monitor("Time=%0t | rst=%0b | req=%0b |  din_master=%0b   |   dout_slave=%0b |  din_slave=%0b | dout_master=%0b  "  
		 ,$time,     rst,      req,       din_master,          dout_slave ,      din_slave ,     dout_master );

        rst = 1;
        #15;
        rst = 0;
        $display("no operation, req = 2'b00");     
        
        din_master = 0;
        din_slave = 0;
	    req = 0;

        wait (mstr_state_tx == 0 && mstr_state_rx == 0);
        $display("master send slave received, req = 2'b01");     
            req = 1;
            wait_duration = 10;
            din_slave = 0;

        repeat(2) begin
            din_master = $urandom_range(1,255);
            @(posedge clk);

	 check_dout_slv();

		wait (done_tx == 1);	
  	end 
     

          //slave send, master received (miso)
        wait (mstr_state_tx == 0 && mstr_state_rx == 0);
        $display("slave send master received, req = 2'b10");     
        req = 2;
        din_master = 0;

        repeat(2) begin
            din_slave = $urandom_range(1, 255);
            @(posedge clk);

	check_dout_mstr();
            wait (done_rx == 1);
        end 

        // full duplex
        wait  (mstr_state_tx == 0 && mstr_state_rx == 0 && slv_state_tx == 0 && slv_state_rx == 0);
        $display("full duplex, req = 2'b11");     
        req = 3;

        repeat(2) begin
            fork
                begin
                    din_slave = $urandom_range(1, 255);
                    check_dout_mstr();
                    wait (done_rx == 1);
                end
                
                begin
                    din_master = $urandom_range(1, 255);
                    check_dout_slv();
                    wait (done_tx == 1);                    
                end
            join

            @(posedge clk);
        end 

        $display("Test complete.");
        $finish;
    end

    initial begin
        $fsdbDumpfile("spi_tb.fsdb");
        $fsdbDumpvars(0, tb_top, "+all");
    end

 

    always_ff @(posedge clk) begin
        if (rst) begin
            expected_dout_slave <= 8'b0;
            expected_dout_master <= 8'b0;
            mstr_bit_received_count  <= 0;
            slv_bit_received_count  <= 0;
        end else begin
            if ((mstr_state_tx == 2) && (req == 1 | req == 3) && sclk_negedge && slv_bit_received_count < 8) begin
                expected_dout_slave <= (expected_dout_slave << 1) | din_master[7 - slv_bit_received_count];
                slv_bit_received_count  <= slv_bit_received_count + 1; 
            end 

            if ((slv_state_tx == 1) && (req == 2 | req == 3) && sclk_negedge && mstr_bit_received_count < 8) begin
                expected_dout_master <= (expected_dout_master << 1) | din_slave[7 - mstr_bit_received_count];
                mstr_bit_received_count  <= mstr_bit_received_count + 1;      
            end

            if (done_tx) begin
                slv_bit_received_count  <= 0;

                if (slv_state_rx && cs) begin
                    expected_dout_slave <= 0;
                end
            end

            if (done_rx) begin
                mstr_bit_received_count  <= 0;
            end
        end
    end



    genvar i;
    generate
    for (i = 0; i < 8; i++) begin : gen_chk_dout_slave
        property chk_dout_slave;
            @(negedge sclk) disable iff (!(req == 1 || req == 3))
                dout_slave[i] |-> expected_dout_slave[i];
        endproperty
 
        property chk_dout_mstr;
            @(negedge sclk) disable iff (!(req == 2 || req == 3))
                dout_master[i] |-> expected_dout_master[i];
        endproperty
        
/*
        property chk_master_tx_done;
            @(posedge sclk) disable iff (!(req == 1 || req == 3))
                (bit_counter_slv == 8)
          
*/  
        //assertion check on when slave send, master received
        assert property (chk_dout_mstr)
            else $error("Mismatch at bit %0d: dmstr_slave != expected_dmstr_slave", i);

        //assertion check on when master send, slave received        
        assert property (chk_dout_slave)
            else $error("Mismatch at bit %0d: dout_slave != expected_dout_slave", i);



    end
    endgenerate

endmodule

    
