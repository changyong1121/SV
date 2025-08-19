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
    logic [(SPI_TRF_BIT-1):0] expected_dout_slave;
    logic [(SPI_TRF_BIT-1):0] expected_dout_master;
    logic [3:0] slv_bit_received_count;     
    logic [3:0] mstr_bit_received_count; 
	logic sclk;
    logic sclk_posedge;
    logic sclk_negedge;
    logic cs;
   
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

    assign sclk = dut.sclk_generator_inst.sclk;
    assign sclk_posedge = dut.spi_master_inst.sclk_posedge;
    assign sclk_negedge = dut.spi_master_inst.sclk_negedge;
    assign cs = dut.spi_master_inst.cs;
    assign req_enable = (!mstr_state_tx && !mstr_state_rx); //&& !slv_state_tx && !slv_state_rx);

    int bit_counter_slv = 0;  // Define in a higher scope
    int bit_counter_mstr = 0;
    int pass_count_slv = 0;
    int fail_count_slv = 0;
    int pass_count_mstr = 0;
    int fail_count_mstr = 0;

     task check_dout_slv();
        @(posedge sclk_negedge);  // Wait for SCLK negedge (flag or direct signal)
        @(posedge clk);           // One cycle later
        #5;
        $display("[check_dout_slv] Time=%0t | Bit %0d | dout_slave = 0x%0b | din_master = 0x%0b", 
             $time, bit_counter_slv, dout_slave, din_master);

        bit_counter_slv++;

        if (bit_counter_slv == SPI_TRF_BIT) begin
            if (dout_slave === din_master) begin
                $display("✅ [PASS] Time=%0t | dout_slave (0x%0b)MATCHES din_master (0x%0b)", $time, dout_slave, din_master);
            pass_count_slv++;
            end else begin
                $display("❌ [FAIL] Time=%0t | dout_slave = 0x%0b, din_master = 0x%0b", $time, dout_slave, din_master);
            fail_count_slv++;
            end
            bit_counter_slv = 0; // Reset counter for next transaction
        end
    endtask

    task check_dout_mstr();
        @(posedge sclk_negedge);  // Wait for SCLK negedge (flag or direct signal)
        @(posedge clk);           // One cycle later
        #5;
        $display("[check_dout_mstr] Time=%0t | Bit %0d | dout_mstr = 0x%0b | din_slave = 0x%0b", 
             $time, bit_counter_mstr, dout_master, din_slave);

        bit_counter_mstr++;

        if (bit_counter_mstr == SPI_TRF_BIT) begin
            if (dout_slave === din_master) begin
                $display("✅ [PASS] Time=%0t | dout_master (0x%0b) MATCHES din_slave (0x%0b)", $time, dout_master, din_slave);
            pass_count_mstr++;
            end else begin
                $display("❌ [FAIL] Time=%0t | dout_master = 0x%0b, din_slave = 0x%0b", $time, dout_master, din_slave);
            fail_count_mstr++;
            end
            bit_counter_mstr = 0; // Reset counter for next transaction
        end
    endtask

    task mstr_send_only();
        req = 1;
        din_slave = 0;
        wait_duration = $urandom_range(10,50);        
        din_master = $urandom_range(1,255);
        @(posedge clk);
  	    repeat (SPI_TRF_BIT) begin
	        check_dout_slv();
        end
    endtask

    task slv_send_only();
        req = 2;
        din_master = 0;
        wait_duration = $urandom_range(10,50);
        din_slave = $urandom_range(1, 255);
        @(posedge clk);
        repeat (SPI_TRF_BIT) begin
	        check_dout_mstr();
        end
    endtask

    task both_mstr_slv_send();
        req = 3;
        wait_duration = $urandom_range(10,50);
        fork
            begin
                din_master = $urandom_range(1,255);
                @(posedge clk);
  	            repeat (SPI_TRF_BIT) begin
	                check_dout_slv();
                end
                wait (done_rx == 1);	
            end

            begin
		        din_slave = $urandom_range(1, 255);
                @(posedge clk);
                repeat (SPI_TRF_BIT) begin
	                check_dout_mstr();
                end
		        wait (done_tx == 1);	                     
            end
        join

        @(posedge clk);
    endtask

    task randomize_test();
        req = $urandom_range(0,3);
        if (req == 0) begin
            wait_duration = $urandom_range(10,50);
            din_master = $urandom_range(1,255);
            din_slave = $urandom_range(1,255);
        end else
        if (req == 1) begin
            mstr_send_only();
            wait (done_tx == 1);
        end else 
        if (req == 2) begin
            slv_send_only();
            wait(done_rx == 1);
        end else
        if (req == 3) begin
            both_mstr_slv_send();
        end
    endtask

       
    task reset_sequence();
        rst = 1;
        #300;
        rst = 0;
    endtask



    covergroup cg @(posedge clk);
	    coverpoint rst;
	    coverpoint req;
	    coverpoint din_master {
		bins low_range = {[0:127]}; 
		bins high_range = {[128:255]};}
	    coverpoint din_slave{
		bins low_range = {[0:127]}; 
		bins high_range = {[128:255]};}
	    coverpoint dout_master;
	    coverpoint dout_slave;
	cross req, din_master;
	cross req, din_slave;

    endgroup

	cg cg_inst;
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

  
    initial begin
        $display("Test start.");     
        cg_inst = new();             
        din_master = 0;
        din_slave = 0;
	    req = 0;

        // Reset sequence
        reset_sequence();
        #10;

        // master send slave received
        wait (req_enable);
        $display("master send slave received, req = 2'b01");     
        repeat(2000) begin
            mstr_send_only();
		    wait (done_tx == 1);	
        end

        // slave send, master received 
        wait (req_enable);
        $display("slave send master received, req = 2'b10");     
        repeat(2000) begin
            slv_send_only();
            wait (done_rx == 1);
        end

        // full duplex
        wait  (req_enable);
        $display("full duplex, req = 2'b11");   
        repeat (1000) begin
            both_mstr_slv_send();
        end  
       
 
        // no operation
        wait  (req_enable);
        $display("No operation, req = 2'b00");     
        req = 0;
        repeat (1) begin
            wait_duration = $urandom_range(10,50);
            din_master = $urandom_range(1,255);
            din_slave = $urandom_range(1,255);
            repeat (200) @(posedge clk);
        end

        // master send, rst asserted
        wait  (req_enable);
        $display("master send slave received, req = 2'b01"); 
        repeat(1) begin
            mstr_send_only();
            wait ((mstr_state_tx == 2) && (slv_bit_received_count == 5)); //At mstr send state assert rst   
            #20;
            reset_sequence();
        end

        /////////////////////
        wait  (req_enable);
        repeat (1) begin
            mstr_send_only(); 
            wait (mstr_state_tx == 3); // At mstr wait state assert rst
            #20;
            reset_sequence();
        end
        
        ////////////////////
         
        wait  (req_enable);
        repeat (1) begin
            mstr_send_only(); 
            wait (mstr_state_tx == 1); // At mstr wait state assert rst
            #20;
            reset_sequence();
        end

        // slave send, rst asserted
        wait (req_enable);
        repeat (1) begin
            $display("slave send master received, req = 2'b10"); 
            slv_send_only();    
            wait (slv_state_tx && (mstr_bit_received_count == 4));
            #20
            reset_sequence();
        end

        wait (req_enable);
        repeat (10) begin
            $display("randomize input test");
            randomize_test();
        end
        
        #20;
        $display("Test complete.");
        $display("\n================== TEST SUMMARY ==================");
        $display("Master send, Slave received : Passed = %0d | Failed = %0d", pass_count_slv, fail_count_slv);
        $display("Slave send, Master received : Passed = %0d | Failed = %0d", pass_count_mstr, fail_count_mstr);
        $display ("Cumulative Coverage = %0.2f %%", cg_inst.get_coverage());
        $display("==================================================");  
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
            if ((req == 1 | req == 3) && sclk_negedge && slv_bit_received_count < 8) begin
                expected_dout_slave <= (expected_dout_slave << 1) | din_master[7 - slv_bit_received_count];
                slv_bit_received_count  <= slv_bit_received_count + 1; 
            end 

            if ((req == 2 | req == 3) && sclk_negedge && mstr_bit_received_count < 8) begin
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

    logic [7:0] wait_done_tx_counter;
    logic wait_done_tx_flag;
    logic wait_done_rx_flag;

 

    always_ff @(posedge clk) begin
        if (rst) begin
            wait_done_tx_counter <= 0;
        end else if (sclk_posedge && slv_bit_received_count == SPI_TRF_BIT) begin
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
         


    always_comb begin
        if ((dout_master == din_slave) && (mstr_bit_received_count == SPI_TRF_BIT)) begin
            wait_done_rx_flag = 1;
        end else begin
            wait_done_rx_flag = 0;
        end
    end
     
       
    genvar i;
    generate
    for (i = 0; i < SPI_TRF_BIT; i++) begin : gen_chk_dout_slave
        property chk_dout_slave; //master in
            @(negedge sclk) disable iff ((!(req == 1 || req == 3)) || rst)
                dout_slave[i] |-> expected_dout_slave[i];
        endproperty
 
        property chk_dout_mstr; //slave in
            @(negedge sclk) disable iff ((!(req == 2 || req ==3)) || rst)
                dout_master[i] |-> expected_dout_master[i];
        endproperty

        //assertion check on when slave send, master received
        assert property (chk_dout_mstr)
            else $error("Mismatch at bit %0d: dmstr_slave != expected_dmstr_slave", i);

        //assertion check on when master send, slave received        
        assert property (chk_dout_slave)
            else $error("Mismatch at bit %0d: dout_slave != expected_dout_slave", i);


    end
    endgenerate

        property chk_mstr_tx_done;
            @(posedge clk) disable iff (!(req == 1 || req == 3) || rst)
                wait_done_tx_flag && (wait_done_tx_counter == wait_duration) |=> ($rose(done_tx));   
        endproperty
      
        property chk_mstr_rx_done;
            @(posedge clk) disable iff (!(req == 2 || req == 3) || rst)
                sclk_negedge && wait_done_rx_flag |=> $rose(done_rx);              
        endproperty

        property chk_sclk_rst;
            @(posedge clk)
                rst |-> !sclk;
        endproperty

        property chk_mstr_slv_state_rst;
            @(posedge clk)
                rst |-> (mstr_state_tx == 0) && (mstr_state_rx == 0) && (slv_state_tx == 0) && (slv_state_rx == 0);
        endproperty

        property no_operation;
            @(posedge clk) disable iff (rst)
                (req == 0) |=> (mstr_state_tx == 0) && (mstr_state_rx == 0) && (slv_state_tx == 0) && (slv_state_rx == 0);
        endproperty
             
  
        // Assertion check on done_tx flag when mstr finish sending
        assert property (chk_mstr_tx_done)
            else $error("Done_tx flag is not asserted after master finish transaction");

        // Assertion check on done_rx flag when mstr finish receiving
        assert property (chk_mstr_rx_done)
            else $error("Done_rx flag is not asserted after master finish receiving");

        // Assertion check on sclk is low when rst is asserted
        assert property (chk_sclk_rst)
            else $error("SCLK is high when reset");

        // Assertion check on master and slave state is IDLE when rst is asserted 
        assert property (chk_mstr_slv_state_rst)
            else $error("Master and slave is not in IDLE state when reset");

        // Assertion check on master and slave state is IDLE when req = 0 
        assert property (no_operation)
            else $error("Master and slave is not in IDLE state when req = 0");

endmodule

    
