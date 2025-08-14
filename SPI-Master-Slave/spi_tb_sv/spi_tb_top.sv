//`timescale 1ns/ps

module tb_top #(
	parameter MASTER_FREQ = 100_000_000,
	parameter SLAVE_FREQ = 1_800_000,
    parameter SPI_MODE = 1,
    parameter SPI_TRF_BIT = 8,
    parameter WAIT_DURATION = 10
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
    logic req_enable;

    assign mstr_state_tx = dut.spi_master_inst.state_tx[1:0];
    assign mstr_state_rx = dut.spi_master_inst.state_rx;
    assign slv_state_tx = dut.spi_slave_inst.state_tx;
    assign slv_state_rx = dut.spi_slave_inst.state_rx;
    assign sclk_senddata= dut.spi_master_inst.sclk;
    assign sclk = dut.sclk_generator_inst.sclk;
    assign sclk_posedge = dut.spi_master_inst.sclk_posedge;
    assign sclk_negedge = dut.spi_master_inst.sclk_negedge;
    assign cs = dut.spi_master_inst.cs;
    assign req_enable = (!mstr_state_tx && !mstr_state_rx && !slv_state_tx && !slv_state_rx);

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
			bit_counter_slv=0;
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
			bit_counter_mstr=0;
			end 
		end	else begin
		$display("Failed");
		end
	endtask


   covergroup cg @(posedge clk);
	coverpoint rst;
	coverpoint req;
	coverpoint din_master;
	coverpoint din_slave;
	coverpoint dout_master;
	coverpoint dout_slave;
   endgroup
	cg cg_inst;
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

  
    //Reset
    initial begin
        $display("Test start.");     
        $monitor("Time=%0t | rst=%0b | req=%0b |  din_master=%0b   |   dout_slave=%0b |  din_slave=%0b | dout_master=%0b  "  
		 ,$time,     rst,      req,       din_master,          dout_slave ,      din_slave ,     dout_master );
        cg_inst = new(); 
        rst = 1;
        #15;
        rst = 0;
        $display("no operation, req = 2'b00");     
       
         
        din_master = 0;
        din_slave = 0;
	    req = 0;

        #10;

        wait (req_enable);
        $display("master send slave received, req = 2'b01");     
            req = 1;
            wait_duration = WAIT_DURATION;
            din_slave = 0;

        repeat(2) begin
            din_master = $urandom_range(1,255);
            @(posedge clk);

	        check_dout_slv();

		    wait (done_tx == 1);	
  	end 
     

        //slave send, master received (miso)
        wait (req_enable);
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
        wait  (req_enable);
        $display("full duplex, req = 2'b11");     
        req = 3;

        repeat(2) begin
            fork
                begin
                    din_slave = $urandom_range(1, 255);
                    wait (done_rx == 1);
                    check_dout_mstr();

                end
                
                begin
                    din_master = $urandom_range(1, 255);
                    wait (done_tx == 1); 
                    check_dout_slv();                   
                end
            join

            @(posedge clk);
        end 
         
        // master send, rst asserted
        wait  (req_enable);
        $display("master send slave received, req = 2'b01"); 
        req = 1;
        din_master = 120; //$urandom_range(1,255);
        wait (mstr_state_tx);
        #300;
        rst = 1;
        #300;
        rst = 0;
        
        #20;
        $display("Test complete.");
	$display ("Cumulative Coverage = %0.2f %%", cg_inst.get_coverage());
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

    logic [4:0] wait_done_tx_counter;
    logic wait_done_tx_flag;
    logic wait_done_rx_flag;

 

    always_ff @(posedge clk) begin
        if (rst) begin
            wait_done_tx_counter <= 0;
        end else if (sclk_posedge && (mstr_state_tx == 2) && slv_bit_received_count == SPI_TRF_BIT) begin
            if (din_master == dout_slave) begin
                wait_done_tx_flag <= 1;
            end
        end

        if (wait_done_tx_flag) begin
            if (wait_done_tx_counter < wait_duration) begin
                wait_done_tx_counter <= wait_done_tx_counter + 1;
            end else if (wait_done_tx_counter == wait_duration) begin
                wait_done_tx_flag <= 0;
                wait_done_tx_counter <= 0;     
            end
        end
     end
         
    logic rx_clk;
    //assign rx_clk = (sclk | sclk_negedge) ; 
    
    always_ff @(posedge clk) begin
        if (sclk | sclk_negedge) 
            rx_clk <= 1;
        else
            rx_clk <= 0;
    end

    always_comb begin
        if ((dout_master == din_slave) && (mstr_bit_received_count == SPI_TRF_BIT)) begin
            wait_done_rx_flag = 1;
        end else begin
            wait_done_rx_flag = 0;
        end
    end
     
       
    genvar i;
    generate
    for (i = 0; i < 8; i++) begin : gen_chk_dout_slave
        property chk_dout_slave; //master in
            @(negedge sclk) disable iff (!(req == 1 || req == 3))
                (mstr_state_tx == 2) |-> (dout_slave[i] == expected_dout_slave[i]);
        endproperty
 
        property chk_dout_mstr; //slave in
            @(negedge sclk) disable iff (!(req == 2 || req ==3))
                (slv_state_tx == 1) |-> (dout_master[i] == expected_dout_master[i]);
        endproperty


        property chk_mstr_tx_done;
            @(posedge clk) disable iff (!(req == 1 || req == 3))
                wait_done_tx_flag && (wait_done_tx_counter == wait_duration) |=> ($rose(done_tx));   
        endproperty
      
        property chk_mstr_rx_done;
            @(negedge rx_clk) disable iff (!(req == 2 || req == 3))
                $rose(wait_done_rx_flag) |=> $rose(done_rx);              
        endproperty

        property chk_sclk_rst;
            @(posedge clk)
                rst |-> !sclk;
        endproperty

        //assertion check on when slave send, master received
        assert property (chk_dout_mstr)
            else $error("Mismatch at bit %0d: dmstr_slave != expected_dmstr_slave", i);

        //assertion check on when master send, slave received        
        assert property (chk_dout_slave)
            else $error("Mismatch at bit %0d: dout_slave != expected_dout_slave", i);

        assert property (chk_mstr_tx_done)
            else $error("Done_tx flag is not asserted after master finish transaction");

        assert property (chk_mstr_rx_done)
            else $error("Done_rx flag is not asserted after master finish receiving");

        assert property (chk_sclk_rst)
            else $error("sclk is toggle when reset");


    end
    endgenerate

endmodule

    
