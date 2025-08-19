class spi_mon extends uvm_monitor;
    `uvm_component_utils(spi_mon)

    int tran_count;
    int tran_index;
    string tran_type;

    virtual spi_if vif;  // Use mon_mp
  
    //virtual spi_if vif;
    uvm_analysis_port #(spi_tran) mon_ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        tran_index = 1;
        mon_ap = new("mon_ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
            `uvm_error("MONITOR", "Virtual interface (mon_mp) not found in config db")
        end
    endfunction

    task run_phase(uvm_phase phase);
        spi_tran tr_dut;

        forever begin
            @(posedge vif.sclk);
            //wait (vif.mon_cb.done == 1);
            tr_dut = spi_tran::type_id::create("tr_dut");
            tr_dut.tx_data = vif.mon_cb.tx_data;
            tr_dut.start = vif.mon_cb.start;
            tr_dut.busy = vif.mon_cb.busy;

            //@(negedge vif.sclk);
            tr_dut.rx_data = vif.mon_cb.rx_data;
            tr_dut.done = vif.mon_cb.done;
            tr_dut.tran_count = this.tran_count;
            tr_dut.tran_index = this.tran_index;
            tr_dut.tran_type = this.tran_type;

           // `uvm_info("MONITOR", $sformatf("Observe %0d/%0d %s tran from DUT: tx_data=0x%h, rx_data=0x%h, start=%b, busy=%b, done=%b",
             //                        tran_index, tran_count, tran_type, tr_dut.tx_data, tr_dut.rx_data, tr_dut.start, tr_dut.busy, tr_dut.done),
			//	     UVM_MEDIUM)

            tran_index++;
            mon_ap.write(tr_dut);
        end
    endtask
endclass

