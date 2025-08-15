class spi_drv extends uvm_driver #(spi_tran);
    `uvm_component_utils(spi_drv)

    virtual spi_if vif; 
 
    uvm_analysis_port #(spi_tran) drv_ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        drv_ap = new("drv_ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
            `uvm_error("DRIVER", "Virtual interspice (drv_cb) not found in config db")
        end
    endfunction

    task run_phase(uvm_phase phase);
        spi_tran tr;
        forever begin
            // Get transaction
            seq_item_port.get_next_item(tr);

            // Wait for rising edge of clk
            @(posedge vif.clk);

            // Drive inputs
            vif.drv_cb.tx_data <= tr.tx_data;
            vif.drv_cb.start   <= 1'b1;

            // Hold start for 1 cycle
            @(posedge vif.clk);
            vif.drv_cb.start <= 1'b0;

            // Wait until transaction is done
            wait (vif.drv_cb.done == 1'b1);

            // Wait one more clock to allow sampling
            @(posedge vif.clk);

            // Optionally pass transaction to analysis port
            drv_ap.write(tr);

            // Finish the item
            seq_item_port.item_done();
        end
    endtask
endclass

