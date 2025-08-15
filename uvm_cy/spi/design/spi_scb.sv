//collect data from monitor(via analysia port)
//compare DUT out & expected DUT

class spi_scb extends uvm_scoreboard;
	`uvm_component_utils(spi_scb)
	
	//implement port to receive transactions
	uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;


	function new (string name, uvm_component parent);
		super.new (name , parent);
		scb_imp = new("scb_imp", this);		
	endfunction

	//Perform actual vs expected comparison
	function void write(spi_tran tr_dut);
		`uvm_info("SCOREBOARD", $sformatf("Checking: start=%0b, tx_data=0x%0h, rx_data=0x%0h, done=%0b",
    							tr_dut.start, tr_dut.tx_data, tr_dut.rx_data, tr_dut.done), UVM_MEDIUM)

	//spi_tran done is done
	if (tr_dut.done)begin
		if (tr_dut.rx_data !== tr_dut.tx_data) begin 
			`uvm_error("SCOREBOARD", $sformatf("Mismatch! TX=0x%0h, RX=0x%0h", 
								      tr_dut.tx_data, tr_dut.rx_data))
    		end else begin
    			`uvm_info("SCOREBOARD", "Transaction passed.", UVM_LOW)
    end
  end
endfunction
endclass
