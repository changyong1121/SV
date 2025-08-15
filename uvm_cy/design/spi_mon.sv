class spi_mon extends uvm_monitor;
	`uvm_component_utils (spi_mon)


	virtual spi_master_controller_if.mon_mp vif; 
	uvm_analysis_port #(spi_tran) mon_ap;

	function new(string name, uvm_component parent);
	   super.new(name,parent);
	   mon_ap = new("mon_ap", this);
	endfunction
	
	function void build_phase(uvm_phase phase);
	   super.build_phase(phase);
	   if(!uvm_config_db#(virtual spi_master_controller_if.mon_mp)::get(this,"","vif",vif))begin
		`uvm_error("Monitor","Virtual interface (mon_mp) not found in config db")
		end
	endfunction

	task run_phase(uvm_phase phase);
		spi_tran tr_dut;
		@(posedge vif.clk_tb);
		
		forever begin
			@(posedge vif.clk_tb);

			tr_dut = spi_tran::type_id::create("tr_dut");
		//	tr_dut.clk = vif.clk_tb
		//	tr_dut.rst_n = vif.rst_n_tb  
			tr_dut.start =  vif.start_tb
			tr_dut.tx_data = vif.tx_data_tb
			tr_dut.rx_data = vif.rx_data_tb
			tr_dut.busy = vif.busy_tb 
			tr_dut.done = vif.done_tb
			tr_dut.sclk = vif.sclk_tb
			tr_dut.mosi = vif.mosi_tb
			tr_dut.miso = vif.miso_tb
			tr_dut.cs_n = vif.cs_n_tb

	   `uvm_info("MONITOR", $sformat("Observe: Start_tb= %b , ",
						   tr_dut.start), UVM_MEDIUM)


	 mon_ap.write(tr_dut);
         end
	endtask
endclass
