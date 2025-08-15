// Driver take transaction from sequencer and drive signal to DUT interface

class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)

  virtual spi_master_controller_if vif;
  uvm_analysis_port #(spi_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

 function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_master_controller_if)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
	spi_tran tr;
	forever begin
		seq_item_port.get_next_item(tr);    // Get transaction from sequencer
	`uvm_info("DRIVER", $sformatf("rst_n =%0b", tr.rst_n),UVM_MEDIUM)


		vif.rst_n_tb = tr.rst_n;
		vif.start_tb = tr.start;
		vif.tx_data_tb = tr.tx_data;
	//	vif.rx_data_tb = tr.rx_data //assume drive by DUT 
	//	vif.sclk_tb = tr.sclk	    //assume drive by DUT
		vif.mosi_tb = tr.mosi;
	//	vif.miso_tb = tr.miso   //assume it out to monitor
		vif.cs_n_tb = tr.cs_n;

	seq_item_port.item_done();
	end
	endtask
endclass


